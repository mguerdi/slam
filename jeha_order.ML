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
  val kbo_fast : term * term -> partial_order
  val mk_multiset_order_of_strict :
        ('a * 'a -> partial_order) -> ('a list) * ('a list) -> partial_order
  val idxs_of_maximal_elements : ('a * 'a -> partial_order) -> 'a list -> (int * bool) list
  val is_maximal : ('a * 'a -> partial_order) -> bool -> 'a -> 'a list -> bool
  val multiset_eq : ('a * 'a -> bool) -> ('a list * 'a list) -> bool
  val multiset_is_greater_reference : ('a * 'a -> bool) -> ('a * 'a -> bool) -> ('a list * 'a list) -> bool
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
  (* FIXME: above is probably a bit wrong, constants with different types might
  be different due to overloading, might need to properly distinguish those from
  logical symbols, etc. *)
  | Fun of term * int

datatype fo_term = 
    FluidOrVar of term
  | App of fo_head * fo_term list

(* encodes types as terms *)
fun type_to_fo_term (T as (TVar _)) = FluidOrVar (Term.dummy_pattern T)
  | type_to_fo_term (T as (TFree _)) = App (Fun (Term.dummy_pattern T, 0), [])
  | type_to_fo_term (Type (name, Ts)) =
      App (
        (* Note: malformed type *)
        Fun (Term.dummy_pattern (Type (name, [])), length Ts),
        map type_to_fo_term Ts
      )

(* Instead of equipping function symbols with their type arguments, we just equip them with their
type as their first argument, Abstractions and Quantifiers are handled as in the paper but note that
KBO only compares arguments, if the function symbols are equal. *)
fun to_fo_term boundTs (t as (Var _)) = FluidOrVar t
  | to_fo_term boundTs (t as (Free (_, T))) = App (Fun (t, 0), [type_to_fo_term T])
  | to_fo_term boundTs (t as (Const (_, T))) = App (Fun (t, 0), [type_to_fo_term T])
  | to_fo_term boundTs (t as (Bound i)) = App (Fun (t, 0), [type_to_fo_term (nth boundTs i)])
  | to_fo_term boundTs t =
      if JTerm.might_be_fluid t
        then FluidOrVar t
        else case t of
          (* FIXME: fresh variables under lambda? *)
          Abs (_, T, u) => App (Lam, [type_to_fo_term T, to_fo_term (T::boundTs) u])
        | (_ $ _) =>
            let
              val (f, ts) = strip_comb t
              val T = fastype_of1 (boundTs, f)
              val T_and_ts =
                if JTerm.is_quantifier f
                  (* The FO type argument of a quantifier is the binder type, not the type of the
                  quantifier, similarly the fo term argument is the lambdas body, not the lambda. *)
                  then
                    let val [Abs(_, T, u)] = ts in
                      [type_to_fo_term T, to_fo_term (T::boundTs) u]
                    end
                  else (type_to_fo_term T :: map (to_fo_term boundTs) ts)
            in
              App (Fun (f, length ts), T_and_ts)
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
  | prec_ord (_, Lam) = LESS
  | prec_ord
      (Fun (Const ("Pure.dummy_pattern", F), F_arity),
      Fun (Const ("Pure.dummy_pattern", G), G_arity))
    = type_prec_ord (F, G)
  (* FIXME: compare arities or ignore? *)
  | prec_ord (Fun f, Fun g) = (prod_ord ho_prec_ord int_ord) (f, g)

(* Modify variable balance, weight balance, check if var y occurs in term. *)
(* mfyVWBc : bool -> typ list -> var_balance -> weight -> fo_headed_term -> term -> bool
              -> var_balance * weight * bool *)
fun mfyVWBc below_lam vb wb (FluidOrVar x) y increment =
      ( add_var increment x vb
      , if increment then wb +++ var_weight else wb --- var_weight
      , x aconv y )
  | mfyVWBc below_lam vb wb (App (f, ss)) y increment =
      let
        val (vb, wb, res) =
          mfyVWBc_tl (below_lam orelse f = Lam) vb wb ss y increment
        val wf = fo_head_weight below_lam f
      in
        (vb, if increment then wb +++ wf else wb --- wf, res)
      end
    (* FIXME: don't ignore types *)
and mfyVWBc_tl below_lam vb wb [] y increment = (vb, wb, false)
  | mfyVWBc_tl below_lam vb wb (s :: ss) y increment =
      let
        val (vb, wb, res) = mfyVWBc below_lam vb wb s y increment
      in
        if not res
          then mfyVWBc_tl below_lam vb wb ss y increment
          else
            let val (vb, wb) = mfyVWB_tl below_lam vb wb ss increment in
              (vb, wb, true)
            end
      end
    (* FIXME: don't ignore types *)
and mfyVWB_tl below_lam vb wb [] increment = (vb, wb)
  | mfyVWB_tl below_lam vb wb (s :: ss) increment =
      let
        val (vb, wb) = mfyVWB below_lam vb wb s increment
      in
        mfyVWB_tl below_lam vb wb ss increment
      end
and mfyVWB below_lam vb wb (FluidOrVar x) increment =
      (add_var increment x vb, if increment then wb +++ var_weight else wb --- var_weight)
    (* FIXME: don't ignore types *)
  | mfyVWB below_lam vb wb (App (f, ss)) increment =
      let
        val (vb, wb) = mfyVWB_tl (below_lam orelse f = Lam) vb wb ss increment
        val wf = fo_head_weight below_lam f
      in
        (vb, if increment then wb +++ wf else wb --- wf)
      end

(* FIXME: need two boundTs everywhere? *)
(* tckbo : bool -> typ list -> var_balance -> weight -> fo_headed_term * fo_headed_term
            -> var_balance * weight * partial_order *)
fun tckbo below_lam vb wb (FluidOrVar x) (FluidOrVar y) =
      let
        val vb = add_var true x vb
        val vb = add_var false y vb
        val res = if x aconv y then SOME EQUAL else NONE
      in
        (vb, wb, res)
      end
  | tckbo below_lam vb wb (FluidOrVar x) (t as App (g, ts)) =
      let
        val (vb, wb, contained) = mfyVWBc below_lam vb wb t x false
        val res = if contained then SOME LESS else NONE
        val vb = add_var true x vb
      in
        (vb, wb +++ var_weight, res)
      end
  (* FIXME: redundant because symmetric to case above *)
  | tckbo below_lam vb wb (s as App (f, ss)) (FluidOrVar y) =
      let
        val (vb, wb, contained) = mfyVWBc below_lam vb wb s y true
        val res = if contained then SOME GREATER else NONE
        val vb = add_var false y vb
      in
        (vb, wb --- var_weight, res)
      end
  | tckbo below_lam vb wb (App (f, ss)) (App (g, ts)) =
      let
        (* lex will only be inspected if f = g, otherwise it is NONE anyways *)
        (* FIXME: and vb, wb? this is relevant for below_lam and esp. boundTs *)
        (* vb, wb do depend on the head: e.g. if f = Lam and g not *)
        val (vb, wb, lex) = tckbo' below_lam vb wb f g ss ts
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
          (* f = g *)
          else if lex = SOME EQUAL then SOME EQUAL
          else if lex = SOME GREATER then G_or_N
          else if lex = SOME LESS then L_or_N
          else NONE
        )
      end
(* tckbo' : bool -> typ list -> var_balance -> weight -> term -> term -> *)
(* FIXME: don't ignore types *)
and tckbo' below_lam vb wb f g ss ts =
      if is_equal (prec_ord (f, g))
        then tckbolex (below_lam orelse f = Lam) vb wb ss ts
        else
          let
            val (vb, wb) = mfyVWB_tl (below_lam orelse f = Lam) vb wb ss true
            val (vb, wb) = mfyVWB_tl (below_lam orelse g = Lam) vb wb ts false
          in
            (vb, wb, NONE)
          end
    (* FIXME: don't ignore types *)
and tckbolex below_lam vb wb [] [] = (vb, wb, SOME EQUAL)
  | tckbolex below_lam vb wb (s :: ss) (t :: ts) =
      let
        val (vb, wb, res) = tckbo below_lam vb wb s t
      in
        if res = SOME EQUAL
          then tckbolex below_lam vb wb ss ts
          else
            let
              val (vb, wb) = mfyVWB_tl below_lam vb wb ss true
              val (vb, wb) = mfyVWB_tl below_lam vb wb ts false
            in
              (vb, wb, res)
            end
      end

val kbo_fast = #3 o uncurry (tckbo false empty_var_balance zero_weight) o apply2 (to_fo_term [])
val kbo = Jeha_Order_Reference.kbo

fun multiset_eq a_eq (m, n) = submultiset a_eq (m, n) andalso submultiset a_eq (n, m)

fun multiset_is_greater_reference a_g a_eq (m, n) =
  let
    (* val a_eq = a_ord #> curry op= EQUAL *)
    (* x - y *)
    fun sub x y = fold (remove1 a_eq) y x
  in
    (* M = N *)
    not (multiset_eq a_eq (m, n)) andalso
    forall (fn x => exists (fn y => a_g (y, x)) (sub m n)) (sub n m)
  end

(* Baader and Nipkow - Term rewriting and all that, Lemma 2.5.6: For strict orders:
    M > N iff. M \<noteq> N \<and> \<forall> m \<in> N-M. \<exists> m \<in> M-N. m > n
M < N := N > M *)
(* FIXME: test against a reference implementation *)
fun mk_multiset_order_of_strict a_ord (m, n) =
  if multiset_is_greater_reference (a_ord #> curry op= (SOME GREATER)) (a_ord #> curry op= (SOME EQUAL)) (m, n)
    then SOME GREATER
  (* NOTE: The commented next line is not the same as the line below it! *)
  (*      multiset_is_greater_reference (a_ord #> curry op= (SOME LESS))    (a_ord #> curry op= (SOME EQUAL)) (m, n) *)
  else if multiset_is_greater_reference (a_ord #> curry op= (SOME GREATER)) (a_ord #> curry op= (SOME EQUAL)) (n, m)
    then SOME LESS
  else if multiset_eq (a_ord #> curry op= (SOME EQUAL)) (m, n)
    then SOME EQUAL
  else NONE

(* FIXME: broken, multiset extension of > is not the same as multiset extension of < *)
(*
  let
    fun a_eq (x, y) = SOME EQUAL = a_ord (x, y)
    val m_minus_n = fold (remove1 a_eq) n m
    val n_minus_m = fold (remove1 a_eq) m n
    (* FIXME: what if empty? *)
    val for_m_exists = map (K false) m
    val for_n_exists = map (K false) n
  in
    if null n_minus_m andalso null m_minus_n
      then SOME EQUAL
      else
        let
          val indexed_m_n_pairs =
            (m_minus_n, n_minus_m)
            |> apply2 (map_index (uncurry pair))
            |> uncurry Jeha_Common.cartesian_product
          val (for_m_exists, for_n_exists) =
            (for_m_exists, for_n_exists)
            |> fold
                (fn ((m_idx, m), (n_idx, n)) =>
                  case a_ord (m, n) of
                    SOME GREATER => apsnd (nth_map n_idx (K true))
                  | SOME LESS => apfst (nth_map m_idx (K true))
                  | _ => I)
                indexed_m_n_pairs
        in
          if forall I for_m_exists
            then SOME GREATER
          else if forall I for_n_exists
            then SOME LESS
          else NONE
        end
  end
*)

(* returns the indices of the maximal elements, marked as strict / non-strict by true / false resp. *)
fun idxs_of_maximal_elements a_ord xs =
  let
    val indexed_xs =  map_index (uncurry pair) xs
    (* SOME true: strict maximal, SOME false: non strict maximal, NONE: not maximal *)
    val maximality_markers = map (K (SOME true)) xs
    (* compare the list elements pairwise and determine which are not (strictly) maximal *)
    val maximality_markers =
      fold
      ( fn (i, x) =>
          fold
          ( fn (j, y) => case a_ord (x, y) of 
                SOME GREATER =>
                  (* y cannot be maximal *)
                  nth_map j (K NONE)
              | SOME LESS =>
                  (* x cannot be maximal *)
                  nth_map i (K NONE)
              | SOME EQUAL => (fn markers =>
                  markers |> (case (nth markers i) of
                    (* x and y are equal, so neither is strict maximal.
                    NOTE: this can only happen with the first y that is equal to x *)
                    SOME true => nth_map j (K (SOME false)) #> nth_map i (K (SOME false))
                  | SOME false => nth_map i (K (SOME false))
                  | NONE => nth_map j (K NONE)))
              | NONE => I
          )
          (* compare with all elements which come later in the list *)
          (drop (i + 1) indexed_xs)
      )
      indexed_xs
      maximality_markers
  in
    maximality_markers
    |> map_index (uncurry pair)
    |> map_filter (fn (idx, is_max) => Jeha_Common.map_some (pair idx) is_max)
  end

fun is_maximal a_ord strict x xs =
  let
    (* NONE = not maximal, SOME strict = strict maximal *)
    val (maximal, occurrences) = 
      fold (fn y => fn (maximal, occurrences) =>
        if maximal andalso (not strict orelse occurrences <= 1)
          then case a_ord (y, x) of
            (* y is strictly greater than x, so x can't be maximal *)
            SOME GREATER => (false, occurrences)
          | SOME EQUAL => (true, occurrences + 1)
          | SOME LESS => (true, occurrences)
          | NONE => (true, occurrences)
          (* early abort *)
          else (false, occurrences))
      xs
      (true, 0)
    in
      maximal andalso (not strict orelse occurrences <= 1)
    end

end;
