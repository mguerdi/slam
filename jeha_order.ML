(* Transfinite Higher Order Knuth Bendix Ordering *)

signature JEHA_ORDER =
sig
  type partial_order = order option
  type weight = int * int
  val plus_weight : weight -> weight -> weight
  val weight_ord : weight ord
  val var_weight : weight
  val const_weight : weight
  val quantifier_weight : bool -> weight
  val bound_weight : weight
  val fo_lambda_weight : weight
  val type_weight : typ -> weight
  val term_weight : bool -> term -> weight
  type var_balance
  val map_balances : (int Termtab.table -> int Termtab.table) -> var_balance -> var_balance
  val map_pos_counter : (int -> int) -> var_balance -> var_balance
  val map_neg_counter : (int -> int) -> var_balance -> var_balance
  val add_var : bool -> term -> var_balance -> var_balance
  val no_pos_balances : var_balance -> bool
  val no_neg_balances : var_balance -> bool
  val kbo : term * term -> partial_order
  val mk_multiset_order_of_strict :
        ('a * 'a -> partial_order) -> ('a list) * ('a list) -> partial_order
  val lit_kbo : JLit.T * JLit.T -> partial_order
  val clause_kbo : JClause.T * JClause.T -> partial_order
end;

structure Jeha_Order: JEHA_ORDER =
struct

infix 6 +++
infix 6 ---

type partial_order = order option

(* (omega, one) represents the number: omega * \<omega> + one * 1 *)
type weight = int * int;

val zero_weight = (0, 0)

fun plus_weight (omega, one) (omega', one') = (omega + omega', one + one')
fun (w +++ w') = plus_weight w w'
fun (w --- (omega', one')) = plus_weight w (~omega', ~one')

(* lexicographic comparison *)
val weight_ord = prod_ord int_ord int_ord

val var_weight = (0, 1)
val const_weight = (0, 1)
(* below lambdas there are only \<forall>' and \<exists>' *)
fun quantifier_weight below_lam = if below_lam then const_weight else (1, 0)
val bound_weight = const_weight
val fo_lambda_weight = const_weight

fun type_weight (Type (_, Ts)) = const_weight +++ fold (curry (op +++)) (map type_weight Ts) zero_weight
  | type_weight (TFree _) = const_weight
  | type_weight (TVar _) = var_weight

fun term_weight _ (Var _) = var_weight
  | term_weight _ (Free _) = const_weight
  | term_weight below_lam (t as (Const _)) =
      if JTerm.is_quantifier t then quantifier_weight below_lam else const_weight
  | term_weight _ (Bound _) = bound_weight
  | term_weight below_lam t =
      if JTerm.might_be_fluid t
        then var_weight (* z\<^sub>t *)
        else case t of
          Abs (_, T, t) => fo_lambda_weight +++ type_weight T +++ term_weight true t
        | (_ $ _) =>
            let val (f, Ts, us) = JTerm.strip_comb_fun_types_args t in 
              (* weight of f, FIXME: pass (f, length (?)) to symbol weight function *)
              const_weight
              (* type args of FO fun. symbol *)
              +++ fold (curry (op +++)) (map type_weight Ts) zero_weight
              +++ (if JTerm.is_quantifier f
                    (* descend directly into body of lambda *)
                    then
                      let val [(Abs (_, _, u))] = us in term_weight below_lam u end
                    else
                      fold (curry (op +++)) (map (term_weight below_lam) us) zero_weight)
            end

(* Fluid terms t are translated to FO via a variable z\<^sub>t, instead of creating a
new variable to store in a Vartab just use a Termtab and store the term
directly. Type vars are stored via typed dummy patterns:
  Const ("Pure.dummy_pattern", TVar x) represents the type variable x
*)
type var_balance =
  { balances: int Termtab.table, pos_balances: int, neg_balances: int }

val empty_var_balance = { balances = Termtab.empty, pos_balances = 0, neg_balances = 0 }

fun map_balances f balance =
  { balances = f (#balances balance)
  , pos_balances = #pos_balances balance
  , neg_balances = #neg_balances balance
  }

fun map_pos_counter f balance =
  { balances = #balances balance
  , pos_balances = f (#pos_balances balance)
  , neg_balances = #neg_balances balance
  }

fun map_neg_counter f balance =
  { balances = #balances balance
  , pos_balances = #pos_balances balance
  , neg_balances = f (#neg_balances balance)
  }

fun add_var (increment : bool) (var : term) balance =
  let
    val new_balances =
      #balances balance |> Termtab.map_default (var, 0) (curry (op +) (if increment then 1 else ~1))
    val new_count = the (Termtab.lookup new_balances var)
    val update_counters =
      if new_count = 1 andalso increment
        then map_pos_counter (curry (op +) 1)
      else if new_count = ~1 andalso not increment
        then map_neg_counter (curry (op +) 1)
      else if new_count = 0
        then if increment
          then map_neg_counter (curry (op +) ~1)
          else map_pos_counter (curry (op +) ~1)
      else I
    in
      balance |> map_balances (K new_balances) |> update_counters
    end

(* FIXME: pass back balance for linearity optimization? *)
fun no_pos_balances balance = 0 = #pos_balances balance
fun no_neg_balances balance = 0 = #neg_balances balance

(* first-order, for reference *)
datatype fo_head =
    Lam
  (* Const or Free and arity *)
  (* FIXME: Delete type information in term below to make sure it's not accidentally being used
  (mismatch between FO and HO quantifier because its Abs is stripped away). *)
  | Fun of term * int

(* top level is FO *)
(* The first order tree has no concept of binders (i.e. the fo_head Lam is not a binder, just a
function symbol), types of Bound variables are stored in an auxilliary list boundTs : typ list. *)
datatype fo_headed_term =
    FluidOrVar of term
  | App of fo_head * term list

(* encodes types as terms *)
fun type_to_term (T as (TVar _)) = Term.dummy_pattern T
  | type_to_term (T as (TFree _)) = Term.dummy_pattern T
  | type_to_term (Type (name, Ts)) =
      Term.list_comb (
        (* Note: malformed type *)
        Term.dummy_pattern (Type (name, [])),
        map type_to_term Ts
      )

(* Instead of equipping function symbols with their type arguments, we just equip them with their
type as their first argument, Abstractions and Quantifiers are handled as in the paper but note that
KBO only compares arguments, if the function symbols are equal. *)
fun to_fo_headed_term1 (boundTs, t as (Var _)) = (boundTs, FluidOrVar t)
  | to_fo_headed_term1 (boundTs, t as (Free (_, T))) = (boundTs, App (Fun (t, 0), [type_to_term T]))
  | to_fo_headed_term1 (boundTs, t as (Const ("Pure.dummy_pattern", TVar _))) =
      (boundTs, FluidOrVar t)
  | to_fo_headed_term1 (boundTs, t as (Const ("Pure.dummy_pattern", TFree _))) =
      (boundTs, App (Fun (t, 0), []))
  | to_fo_headed_term1 (boundTs, t as (Const ("Pure.dummy_pattern", Type (_, [])))) =
      (boundTs, App (Fun (t, 0), []))
  | to_fo_headed_term1 (boundTs, t as (Const ("Pure.dummy_pattern", Type (_, (_::_))))) =
      error "Type should not have args"
  | to_fo_headed_term1 (boundTs, t as (Const (_, T))) = (boundTs, App (Fun (t, 0), [type_to_term T]))
  | to_fo_headed_term1 (boundTs, t as (Bound i)) = (boundTs, App (Fun (t, 0), [type_to_term (nth boundTs i)]))
  | to_fo_headed_term1 (boundTs, t) =
      if JTerm.might_be_fluid t
        then (boundTs, FluidOrVar t)
        else case t of
          (* FIXME: fresh variables under lambda? *)
          Abs (_, T, u) => (T::boundTs, App (Lam, [type_to_term T, u]))
        | (_ $ _) =>
            let
              val (f, ts) = strip_comb t
              val T = fastype_of1 (boundTs, f)
              val (boundTs, T_and_ts) =
                if JTerm.is_quantifier f
                  (* The FO type argument of a quantifier is the binder type, not the type of the
                  quantifier, similarly the fo term argument is the lambdas body, not the lambda. *)
                  then let val [Abs(_, T, u)] = ts in (T::boundTs, [type_to_term T, u]) end
                  else (boundTs, type_to_term T :: ts)
            in
              (boundTs, App (Fun (f, length ts), T_and_ts))
            end

fun fo_head_weight below_lam Lam = fo_lambda_weight
  | fo_head_weight below_lam (Fun (f, _)) =
      if JTerm.is_quantifier f then quantifier_weight below_lam else const_weight

fun ho_prec_ord ((Const ("Pure.dummy_pattern", _), _)) = error "dummy pattern in ho_prec_ord"
  | ho_prec_ord (_, (Const ("Pure.dummy_pattern", _))) = error "dummy pattern in ho_prec_ord"
  | ho_prec_ord (Bound i, Bound j) = int_ord (i, j)
  | ho_prec_ord (Bound _, _) = GREATER
  | ho_prec_ord (_, Bound _) = LESS
  | ho_prec_ord (Const (@{const_name HOL.All}, _), Const (@{const_name HOL.All}, _)) = EQUAL
  | ho_prec_ord (Const (@{const_name HOL.All}, _), _) = GREATER
  | ho_prec_ord (_, Const (@{const_name HOL.All}, _)) = LESS
  | ho_prec_ord (Const (@{const_name HOL.Ex}, _), Const (@{const_name HOL.Ex}, _)) = EQUAL
  | ho_prec_ord (Const (@{const_name HOL.Ex}, _), _) = GREATER
  | ho_prec_ord (_, Const (@{const_name HOL.Ex}, _)) = LESS
  (* full case distinctions for False and True (lowest precedence) *)
  | ho_prec_ord (Const (@{const_name HOL.True}, _), Const (@{const_name HOL.True}, _)) = EQUAL
  | ho_prec_ord (Const (@{const_name HOL.True}, _), _) = LESS
  | ho_prec_ord (Const (@{const_name HOL.False}, _), Const (@{const_name HOL.False}, _)) = EQUAL
  | ho_prec_ord (Const (@{const_name HOL.False}, _), Const (@{const_name HOL.True}, _)) = GREATER
  | ho_prec_ord (Const (@{const_name HOL.False}, _), _) = LESS
  (* FIXME: user-defined *)
  | ho_prec_ord (Const (f, _), Const (g, _)) = string_ord (f, g)
  | ho_prec_ord (Const _, _) = GREATER
  | ho_prec_ord (_, Const _) = LESS
  | ho_prec_ord (Free (f, _), Free (g, _)) = string_ord (f, g)
  | ho_prec_ord (Free _, _) = GREATER
  | ho_prec_ord (_, Free _) = LESS

(* FIXME: user-defined *)
fun type_prec_ord (Type (_, _::_), _) = error "Type should not have args"
  | type_prec_ord (_, Type (_, _::_)) = error "Type should not have args"
  | type_prec_ord (TVar _, _) = error "TVar in type_prec_ord"
  | type_prec_ord (_, TVar _) = error "TVar in type_prec_ord"
  | type_prec_ord (Type (F, []), Type (G, [])) = string_ord (F, G)
  | type_prec_ord (Type _, _) = GREATER
  | type_prec_ord (_, Type _) = LESS
  (* FIXME: ignoring sorts? *)
  | type_prec_ord (TFree (F, _), TFree (G, _)) = string_ord (F, G)
  | type_prec_ord (TFree _, _) = GREATER
  | type_prec_ord (_, TFree _) = LESS

(* prec_ord : fo_head ord *)
(* FIXME: irreflexive? total? *)
(* lam > db > quantifier > symbols > bot > top *)
fun prec_ord (Lam, Lam) = EQUAL
  | prec_ord (Lam, _) = GREATER
  | prec_ord
      (Fun (Const ("Pure.dummy_pattern", F), F_arity),
      Fun (Const ("Pure.dummy_pattern", G), G_arity))
    = type_prec_ord (F, G)
  (* FIXME: compare arities or ignore? *)
  | prec_ord (Fun f, Fun g) = (prod_ord ho_prec_ord int_ord) (f, g)

(* Modify variable balance, weight balance, check if var y occurs in term. *)
(* mfyVWBc : bool -> typ list -> var_balance -> weight -> fo_headed_term -> term -> bool
              -> var_balance * weight * bool *)
fun mfyVWBc below_lam boundTs vb wb (FluidOrVar x) y increment =
      ( add_var increment x vb
      , if increment then wb +++ var_weight else wb --- var_weight
      , x aconv y )
  | mfyVWBc below_lam boundTs vb wb (App (f, ss)) y increment =
      let
        val (vb, wb, res) =
          mfyVWBc_tl (below_lam orelse f = Lam) boundTs vb wb ss y increment
        val wf = fo_head_weight below_lam f
      in
        (vb, if increment then wb +++ wf else wb --- wf, res)
      end
    (* FIXME: don't ignore types *)
and mfyVWBc_tl below_lam boundTs vb wb [] y increment = (vb, wb, false)
  | mfyVWBc_tl below_lam boundTs vb wb (s :: ss) y increment =
      let
        val (vb, wb, res) = let val (boundTs, s) = to_fo_headed_term1 (boundTs, s) in
          mfyVWBc below_lam boundTs vb wb s y increment
        end
      in
        if not res
          then mfyVWBc_tl below_lam boundTs vb wb ss y increment
          else
            let val (vb, wb) = mfyVWB_tl below_lam boundTs vb wb ss increment in
              (vb, wb, true)
            end
      end
    (* FIXME: don't ignore types *)
and mfyVWB_tl below_lam boundTs vb wb [] increment = (vb, wb)
  | mfyVWB_tl below_lam boundTs vb wb (s :: ss) increment =
      let
        val (vb, wb) = let val (boundTs, s) = to_fo_headed_term1 (boundTs, s) in
           mfyVWB below_lam boundTs vb wb s increment
        end
      in
        mfyVWB_tl below_lam boundTs vb wb ss increment
      end
and mfyVWB below_lam boundTs vb wb (FluidOrVar x) increment =
      (add_var increment x vb, if increment then wb +++ var_weight else wb --- var_weight)
    (* FIXME: don't ignore types *)
  | mfyVWB below_lam boundTs vb wb (App (f, ss)) increment =
      let
        val (vb, wb) = mfyVWB_tl (below_lam orelse f = Lam) boundTs vb wb ss increment
        val wf = fo_head_weight below_lam f
      in
        (vb, if increment then wb +++ wf else wb --- wf)
      end

(* FIXME: need two boundTs everywhere? *)
(* tckbo : bool -> typ list -> var_balance -> weight -> fo_headed_term * fo_headed_term
            -> var_balance * weight * partial_order *)
fun tckbo below_lam boundTs vb wb (FluidOrVar x) (FluidOrVar y) =
      let
        val vb = add_var true x vb
        val vb = add_var false y vb
        val res = if x aconv y then SOME EQUAL else NONE
      in
        (vb, wb, res)
      end
  | tckbo below_lam boundTs vb wb (FluidOrVar x) (t as App (g, ts)) =
      let
        val (vb, wb, contained) = mfyVWBc below_lam boundTs vb wb t x false
        val res = if contained then SOME LESS else NONE
        val vb = add_var true x vb
      in
        (vb, wb +++ var_weight, res)
      end
  (* FIXME: redundant because symmetric to case above *)
  | tckbo below_lam boundTs vb wb (s as App (f, ss)) (FluidOrVar y) =
      let
        val (vb, wb, contained) = mfyVWBc below_lam boundTs vb wb s y true
        val res = if contained then SOME GREATER else NONE
        val vb = add_var false y vb
      in
        (vb, wb --- var_weight, res)
      end
  | tckbo below_lam boundTs vb wb (App (f, ss)) (App (g, ts)) =
      let
        val (vb, wb, lex) = tckbo' below_lam boundTs vb wb f g ss ts
        val wb = wb +++ fo_head_weight below_lam f --- fo_head_weight below_lam g
        val nNeg = no_neg_balances vb
        val nPos = no_pos_balances vb
        val G_or_N = if nNeg then SOME GREATER else NONE
        val L_or_N = if nPos then SOME LESS else NONE
        val f_comp_g = prec_ord (f, g)
      in
        (
          vb,
          wb,
          if is_greater (weight_ord (wb, zero_weight)) then G_or_N
          else if is_less (weight_ord (wb, zero_weight)) then L_or_N
          else if is_greater f_comp_g then G_or_N
          else if is_less f_comp_g then L_or_N
          else if not (is_equal f_comp_g) then NONE
          else if lex = SOME EQUAL then SOME EQUAL
          else if lex = SOME GREATER then G_or_N
          else if lex = SOME LESS then L_or_N
          else NONE
        )
      end
(* tckbo' : bool -> typ list -> var_balance -> weight -> term -> term -> *)
(* FIXME: don't ignore types *)
and tckbo' below_lam boundTs vb wb f g ss ts =
      if is_equal (prec_ord (f, g))
        then tckbolex (below_lam orelse f = Lam) boundTs vb wb ss ts
        else
          let
            val (vb, wb) = mfyVWB_tl (below_lam orelse f = Lam) boundTs vb wb ss true
            val (vb, wb) = mfyVWB_tl (below_lam orelse g = Lam) boundTs vb wb ts false
          in
            (vb, wb, NONE)
          end
    (* FIXME: don't ignore types *)
and tckbolex below_lam boundTs vb wb [] [] = (vb, wb, SOME EQUAL)
  | tckbolex below_lam boundTs vb wb (s :: ss) (t :: ts) =
      let val (vb, wb, res) =
        let
          val (s_boundTs, s) = to_fo_headed_term1 (boundTs, s)
          (* FIXME: now we'll have two, possibly disagreeing boundTs: *)
          val (t_boundTs, t) = to_fo_headed_term1 (boundTs, t)
          (* FIXME: hack *)
          val boundTs = if length t_boundTs > length s_boundTs then t_boundTs else s_boundTs
        in
          tckbo below_lam boundTs vb wb s t
        end
      in
        if res = SOME EQUAL
          then tckbolex below_lam boundTs vb wb ss ts
          else
            let
              val (vb, wb) = mfyVWB_tl below_lam boundTs vb wb ss true
              val (vb, wb) = mfyVWB_tl below_lam boundTs vb wb ts false
            in
              (vb, wb, res)
            end
      end

fun kbo (s, t) =
  let
    val (s_boundTs, s) = to_fo_headed_term1 ([], s)
    (* FIXME: now we'll have two, possibly disagreeing boundTs: (doesn't matter right because we're ignoring types *)
    val (t_boundTs, t) = to_fo_headed_term1 ([], t)
    (* FIXME: hack *)
    val boundTs = if [] = s_boundTs then t_boundTs else s_boundTs
  in
    #3 (tckbo false boundTs empty_var_balance zero_weight s t)
  end

(* Baader and Nipkow - Term rewriting and all that, Lemma 2.5.6 *)
fun mk_multiset_order_of_strict a_ord (m, n) =
  let
    fun a_eq (x, y) = SOME EQUAL = a_ord (x, y)
  in
    if submultiset a_eq (m, n) andalso submultiset a_eq (n, m)
      then SOME EQUAL
      else
        let
          val m_minus_n = fold (remove1 a_eq) n m
          val n_minus_m = fold (remove1 a_eq) m n
          val all_greater =
            n_minus_m |> forall (fn x =>
              m_minus_n |> exists (fn y => SOME GREATER = a_ord (y, x)))
          val all_smaller =
            n_minus_m |> forall (fn x =>
              m_minus_n |> exists (fn y => SOME LESS = a_ord (y, x)))
        in
          if all_greater
            then SOME GREATER
          else if all_smaller
            then SOME LESS
          else NONE
        end
  end

fun map_some _ NONE = NONE
  | map_some f (SOME x) = SOME (f x)

(* see notes in info/master/kbo/build/main.pdf *)
fun lit_kbo (st as (s, t, st_pos), uv as (u, v, uv_pos)) =
  if not st_pos andalso uv_pos
    (* compare negative to positive (note: never equal) *)
    then
      (* FIXME: merge the two traversals into one *)
      if [u, v] |> forall (fn n => [s, t] |> exists (fn m =>
          the_default false (map_some is_greater_equal (kbo (m, n)))))
        (* negative > positive iff. \<forall>\<dots>\<exists>\<dots> m \<ge> n *)
        then SOME GREATER
      else if [u, v] |> forall (fn n => [s, t] |> exists (fn m =>
                the_default false (map_some is_less (kbo (m, n)))))
        (* negative < positive iff. \<forall>\<dots>\<exists>\<dots> m > n *)
        then SOME LESS
      else NONE
  else if st_pos andalso not uv_pos
    (* compare positive to negative by swapping and reversing the result *)
    then map_some rev_order (lit_kbo (uv, st))
  (* same signs *)
  else mk_multiset_order_of_strict kbo ([s, t], [u, v])

val clause_kbo =  mk_multiset_order_of_strict lit_kbo o apply2 JClause.literals

(* Eligibility without selection functions:
Definition 22 (Eligibility) A literal L is (strictly) \<ge>-eligible w.r.t. a substitution \<sigma> in C for
some relation \<ge> if L\<sigma> is (strictly) \<ge>-maximal in C\<sigma>.
The \<ge>-eligible positions of clause C w.r.t a substitution \<sigma> are inductively defined as follows:
(E2) If a literal L = s \<doteq> t with \<not> (s\<sigma> \<le> t\<sigma>) is either \<ge>-eligible and negative or strictly
      \<ge>-eligible and positive, then L.s.\<epsilon> is \<ge>-eligible.
(E2.1) L.s.\<epsilon> if L = (s = t) with \<not> (s\<sigma> \<le> t\<sigma>) is strictly \<ge>-eligible.
(E2.2) L.s.\<epsilon> if L = (s \<noteq> t) with \<not> (s\<sigma> \<le> t\<sigma>) is \<ge>-eligible.
(E3) ...
(E4) ...
*)

end;