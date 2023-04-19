(* Transfinite Higher Order Knuth Bendix Ordering *)

(* FIXME: this is a reference implementation, optmize *)

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
  val add_type : bool -> typ -> var_balance -> var_balance
  val add_term : bool -> term -> var_balance -> var_balance
  val no_pos_balances : var_balance -> bool
  val no_neg_balances : var_balance -> bool
  val var_check : term * term -> partial_order
  val kbo : term * term -> partial_order
end;

structure Jeha_Order: JEHA_ORDER =
struct

infix 6 +++
infix 6 ---

type partial_order = order option

exception Uncomparable

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
      if Jeha_Lang.is_quantifier t then quantifier_weight below_lam else const_weight
  | term_weight _ (Bound _) = bound_weight
  | term_weight below_lam t =
      if Jeha_Lang.might_be_fluid t
        then var_weight (* z\<^sub>t *)
        else case t of
          Abs (_, T, t) => fo_lambda_weight +++ type_weight T +++ term_weight true t
        | (_ $ _) =>
            let val (f, Ts, us) = Jeha_Lang.strip_comb_fun_types_args t in 
              (* weight of f, FIXME: pass (f, length (?)) to symbol weight function *)
              const_weight
              (* type args of FO fun. symbol *)
              +++ fold (curry (op +++)) (map type_weight Ts) zero_weight
              +++ (if Jeha_Lang.is_quantifier f
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

fun add_type increment (Type (_, Ts)) = fold (add_type increment) Ts
  | add_type _ (TFree _) = I
  (* use dummy pattern to store types as terms FIXME: check that this doesn't break when dummy
  patterns are in the input problem (can this even happen?), maybe just use a new custom constant
  instead of "Pure.dummy_pattern"? *)
  | add_type increment (T as (TVar x)) = add_var increment (Term.dummy_pattern T)

fun add_term increment (t as (Var _)) = add_var increment t
  | add_term _ (Free _) = I
  | add_term _ (Const _) = I
  | add_term _ (Bound 0) = I
  | add_term increment t =
      if Jeha_Lang.might_be_fluid t
        then add_var increment t
        else case t of
          (* FIXME: separate variable occurences below lambdas (if that is the correct reading of
          o\<lambda>Sup paper, p. 28. Maybe use (dummy $ Var x) to distinguish below lambdas. *)
          Abs (_, T, t) => add_type increment T #> add_term increment t
        | (_ $ _) =>
            let val (f, Ts, us) = Jeha_Lang.strip_comb_fun_types_args t in 
              fold (add_type increment) Ts #>
                (if Jeha_Lang.is_quantifier f
                  (* descend directly into body of lambda *)
                  then let val [(Abs (_, _, u))] = us in add_term increment u end
                  else fold (add_term increment) us)
            end

(* FIXME: pass back balance for linearity optimization? *)
fun no_pos_balances balance = 0 = #pos_balances balance
fun no_neg_balances balance = 0 = #neg_balances balance

(* check if for all variables x in s and t: |s|\<^sub>x \<le> |t|\<^sub>x *)
fun var_check (s, t) =
  let val balance = empty_var_balance |> add_term false s |> add_term true t in
    (* balance is t - s *)
    (case (no_neg_balances balance, no_pos_balances balance) of
      (false, false) => NONE
    | (false, true) => SOME GREATER
    | (true, false) => SOME LESS
    | (true, true) => SOME EQUAL)
  end

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
  | App of fo_head * typ list * term list

fun to_fo_headed_term1 (boundTs, t as (Var _)) = (boundTs, FluidOrVar t)
  | to_fo_headed_term1 (boundTs, t as (Free _)) = (boundTs, App (Fun (t, 0), [], []))
  | to_fo_headed_term1 (boundTs, t as (Const _)) = (boundTs, App (Fun (t, 0), [] , []))
  | to_fo_headed_term1 (boundTs, t as (Bound _)) = (boundTs, App (Fun (t, 0), [], []))
  | to_fo_headed_term1 (boundTs, t) =
      if Jeha_Lang.might_be_fluid t
        then (boundTs, FluidOrVar t)
        else case t of
          (* FIXME: fresh variables under lambda? *)
          Abs (_, T, u) => (T::boundTs, App (Lam, [T], [u]))
        | (_ $ _) =>
            let
              val (f, Ts, ts) = Jeha_Lang.strip_comb_fun_types_args1 (boundTs, t)
              val (boundTs, Ts, ts) =
                if Jeha_Lang.is_quantifier f
                  (* the FO type argument of a quantifier is the binder type, not the type of the
                  lambda *)
                  then let val [Abs(_, T, u)] = ts in (T::boundTs, [T], [u]) end
                  else (boundTs, Ts, ts)
            in
              (boundTs, App (Fun (f, length ts), Ts, ts))
            end

fun fo_head_weight below_lam Lam = fo_lambda_weight
  | fo_head_weight below_lam (Fun (f, _)) =
      if Jeha_Lang.is_quantifier f then quantifier_weight below_lam else const_weight

fun ho_prec_ord (Bound i, Bound j) = int_ord (i, j)
  | ho_prec_ord (Bound _, _) = GREATER
  | ho_prec_ord (Const (@{const_name HOL.All}, _), Const (@{const_name HOL.All}, _)) = EQUAL
  | ho_prec_ord (Const (@{const_name HOL.All}, _), _) = GREATER
  | ho_prec_ord (Const (@{const_name HOL.Ex}, _), Const (@{const_name HOL.Ex}, _)) = EQUAL
  | ho_prec_ord (Const (@{const_name HOL.Ex}, _), _) = GREATER
  (* full case distinctions for False and True *)
  | ho_prec_ord (Const (@{const_name HOL.False}, _), Const (@{const_name HOL.False}, _)) = EQUAL
  | ho_prec_ord (Const (@{const_name HOL.False}, _), _) = LESS
  | ho_prec_ord (Const (@{const_name HOL.True}, _), Const (@{const_name HOL.True}, _)) = EQUAL
  | ho_prec_ord (Const (@{const_name HOL.True}, _), Const (@{const_name HOL.False}, _)) = GREATER
  | ho_prec_ord (Const (@{const_name HOL.True}, _), _) = LESS
  (* FIXME: user-defined *)
  | ho_prec_ord (Const (f, _), Const (g, _)) = string_ord (f, g)
  | ho_prec_ord (Const _, _) = GREATER
  | ho_prec_ord (Free (f, _), Free (g, _)) = string_ord (f, g)
  | ho_prec_ord (Free _, _) = GREATER

(* prec_ord : fo_head ord *)
(* FIXME: irreflexive? total? *)
(* lam > db > quantifier > symbols > bot > top *)
fun prec_ord (Lam, Lam) = EQUAL
  | prec_ord (Lam, _) = GREATER
  | prec_ord (Fun f_ar, Fun g_ar) = (prod_ord ho_prec_ord int_ord) (f_ar, g_ar)

(*
fun type_kbo (S as (Type (F, Ss)), T as (Type (G, Ts))) =
  let
    val vc = var_check (Term.dummy_pattern S, Term.dummy_pattern T)
    val vc = vc = SOME LESS orelse vc = SOME EQUAL
    val wS = type_weight S
    val wT = type_weight T
  in
    vc andalso
      (is_less (weight_ord (wS, wT))
        orelse
          (wS = wT andalso
            (is_less (prec_type_ord (F, G)) orelse
              (F = G andalso
                kbolex_types (Ss, Ts)
              )
            )
          )
      )
  end

and kbolex_types ([], []) = false
  | kbolex_types (S :: Ss, T :: Ts) =
      if S = T
        then kbolex_types (Ss, Ts)
        else type_kbo (S, T)

fun kbo below_lam (s, t) =
  let
    val vc = var_check (s, t)
    val vc = vc = SOME LESS orelse vc = SOME EQUAL
  in
    fo_headed_kbo
      below_lam
      vc
      (term_weight below_lam s)
      (term_weight below_lam t)
      (to_fo_headed_term s, to_fo_headed_term t)
  end

and fo_headed_kbo below_lam vc ws wt (App (f, sTs, ss), App (g, tTs, ts)) =
      vc andalso
        (is_less (weight_ord (ws, wt))
          orelse
            (ws = wt andalso
              (is_less (prec_ord (f, g)) orelse
                (f = g andalso
                  let val below_lam = below_lam orelse f = Lam in
                    (kbolex_types (sTs, tTs) orelse kbolex_terms below_lam (ss, ts))
                  end ))))
  | fo_headed_kbo _ _ _ _ (FluidOrVar s, FluidOrVar t) = s aconv t
  | fo_headed_kbo _ _ _ _ (FluidOrVar s, App (_, _, ts)) = exists (exists_subterm (curry (op aconv) s)) ts
  | fo_headed_kbo _ _ _ _ _ = false

and kbolex_terms _ ([], []) = false
  | kbolex_terms below_lam (s :: ss, t :: ts) =
      if s aconv t
        then kbolex_terms below_lam (ss, ts)
        else kbo below_lam (s, t)
*)

(*
fun kbo below_lam ((s as (_ $ _)), (t as (_ $ _))) =


fun kbo_comb_comb below_lam (s, t) =
    let
      val (f, sTs, ss) = strip_comb s
      val (g, tTs, ts) = strip_comb t
      (* pair higher order function symbols with their arities *)
      val f = (f, length ss)
      val g = (g, length ts)
      val vc = var_check (s, t)
      val ws = term_weight s
      val wt = term_weight t
    in
      (* vc \<and> (ws < wt \<or> (ws = wt \<and> ( f < g \<or> ( f = g \<and> kbolext1_types () \<and> kbolex (ss, ts))))) *)
      vc andalso (ws < wt orelse (ws = wt andalso (f < g orelse (f = g andalso (kbolex_types (sTs, tTs) orelse kblex1_terms (ss, ts))))))
    end

(* s is a var or might be fluid *)
fun kbo1_var (s, t) = exists_subterm (curry (op aconv) s) t

fun kbolex1_types = error "kbolex1_types unimplemented"
fun kbolex1_terms : Termlist Termlist \<rightarrow> Bool
  | kbolex1_terms ([], []) = false
  | kbolex1_terms (s :: ss, t :: ts) = if s = t then kbolex1(ss, ts) else kbo1 (s, t)

*)


(*

datatype fo_symbol =
    Lam
  (* Const _ or Free _ paired with arity *)
  | Fun of term * int

fun fo_symbol_eq (Lam, Lam) = true
  | fo_symbol_eq (Forall, Forall) = true
  | fo_symbol_eq (Exists, Exists) = true
  | fo_symbol_eq (Fun (f, fAr), Fun (g, gAr)) = f aconv g andalso fAr = gAr

datatype fo_term =
    FluidOrVar of term
  | Type of typ
  | App of fo_symbol * fo_term list

fun to_fo_term1 (_, t as (Var _)) = FluidOrVar t
  | to_fo_term1 (_, t as (Free _)) = App (Fun (t, 0), [])
  | to_fo_term1 (_, t as (Const _)) = App (Fun (t, 0), [])
  | to_fo_term1 (_, t as (Bound _)) = App (Fun (t, 0), [])
  | to_fo_term1 (boundTs, t) =
      if Jeha_Lang.might_be_fluid t
        then FluidOrVar t
        else case t of
          (* FIXME: fresh variables under lambda *)
          Abs (_, T, u) => App (Lam, [Type T, to_fo_term1 (T::boundTs, u)])
        | (_ $ _) =>
            let
              val (f, Ts, ts) = Jeha_Lang.strip_comb_fun_types_args1 (boundTs, t)
            in
              let
                val (boundTs, ts) =
                  if is_quantifier f then
                    let val [Abs(_, T, u)] = ts in (T::boundTs, [u]) end
                    else (boundTs, ts)
              in
                App (Fun (f, length ts), map Type Ts @ map (curry to_fo_term1 boundTs) ts)
              end
            end

fun to_fo_term t = to_fo_term1 ([], t)

fun fo_symbol_weight Lam = fo_lambda_weight
  | fo_symbol_weight below_lam (Fun )

fun fo_term_weight (FluidOrVar _) = var_weight
  | fo_term_weight (Type T) = type_weight T
  | fo_term_weight (App (f, ts)) = term_weight f +++ fold (curry (op +++)) ts (0, 0)

fun add_fo_term increment (FluidOrVar t) = add_var increment t
  | add_fo_term increment (Type T)  = add_type increment T
  | add_fo_term increment (App (_, ts)) = fold (add_fo_term increment) ts

(* check if for all variables x in s and t: |s|\<^sub>x \<le> |t|\<^sub>x *)
fun fo_var_check (s, t) =
  let val balance = empty_var_balance |> add_fo_term false s |> add_fo_term true t in
    (* balance is t - s *)
    (case (no_neg_balances balance, no_pos_balances balance) of
      (false, false) => NONE
    | (false, true) => SOME GREATER
    | (true, false) => SOME LESS
    | (true, true) => SOME EQUAL)
  end

fun fo_kbo below_lam (s as App (f, ss), t as App (g, ts)) =
      let
        val vc = fo_var_check (s, t)
        val vc = vc = SOME LESS orelse vc = SOME EQUAL
        val ws = fo_term_weight s
        val wt = fo_term_weight t
      in
        vc andalso
          (
            is_less (weight_ord (ws, wt)) orelse
              (
                ws = wt andalso
                  (
                    is_less (prec_ord (f, g)) orelse
                      (
                        (* FIXME: aconv or = ? *)
                        fo_symbol_eq (f, g) andalso fo_kbolex below_lam (ss, ts)
                      )
                  )
              )
          )
      end
  | fo_kbo _ (Type S, Type T) = type_kbo (S, T)

and fo_kbolex below_lam ([], []) = false
  | fo_kbolex below_lam (s :: ss, t :: ts) =
      if s aconv t then fo_kbolex below_lam (ss, ts) else fo_kbo below_lam (s, t)

(*
kbo (F( f, ss), F(g, ts)) =
let vc = varCheck1 (F( f, ss), F(g, ts))
ws = phi(F( f, ss))
wt = phi(F(g, ts))
in vc \<and> (ws > wt \<or> (ws = wt \<and> ( f >F g \<or> ( f = g \<and> kbolex(ss, ts)))))
*)

*)

(* Modify variable balance, weight balance, check if var y occurs in term. *)
(* mfyVWBc : bool -> typ list -> var_balance -> weight -> fo_headed_term -> term -> bool
              -> var_balance * weight * bool *)
fun mfyVWBc below_lam boundTs vb wb (FluidOrVar x) y increment =
      ( add_var increment x vb
      , if increment then wb +++ var_weight else wb --- var_weight
      , x aconv y )
  | mfyVWBc below_lam boundTs vb wb (App (f, sTs, ss)) y increment =
      let
        val (vb, wb, res) =
          mfyVWBc_tl (below_lam orelse f = Lam) boundTs vb wb (sTs, ss)  y increment
        val wf = fo_head_weight below_lam f
      in
        (vb, if increment then wb +++ wf else wb --- wf, res)
      end
    (* FIXME: don't ignore types *)
and mfyVWBc_tl below_lam boundTs vb wb (_, []) y increment = (vb, wb, false)
  | mfyVWBc_tl below_lam boundTs vb wb (_, s :: ss) y increment =
      let
        val (vb, wb, res) = let val (boundTs, s) = to_fo_headed_term1 (boundTs, s) in
          mfyVWBc below_lam boundTs vb wb s y increment
        end
      in
        if not res
          then mfyVWBc_tl below_lam boundTs vb wb ([](*FIXME*), ss) y increment
          else
            let val (vb, wb) = mfyVWB_tl below_lam boundTs vb wb ([](*FIXME*), ss) increment in
              (vb, wb, true)
            end
      end
    (* FIXME: don't ignore types *)
and mfyVWB_tl below_lam boundTs vb wb (_, []) increment = (vb, wb)
  | mfyVWB_tl below_lam boundTs vb wb (_, s :: ss) increment =
      let
        val (vb, wb) = let val (boundTs, s) = to_fo_headed_term1 (boundTs, s) in
           mfyVWB below_lam boundTs vb wb s increment
        end
      in
        mfyVWB_tl below_lam boundTs vb wb ([](*FIXME*), ss) increment
      end
and mfyVWB below_lam boundTs vb wb (FluidOrVar x) increment =
      (add_var increment x vb, if increment then wb +++ var_weight else wb --- var_weight)
    (* FIXME: don't ignore types *)
  | mfyVWB below_lam boundTs vb wb (App (f, _, ss)) increment =
      let
        val (vb, wb) = mfyVWB_tl (below_lam orelse f = Lam) boundTs vb wb ([](*FIXME*), ss) increment
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
  | tckbo below_lam boundTs vb wb (FluidOrVar x) (t as App (g, _, ts)) =
      let
        val (vb, wb, contained) = mfyVWBc below_lam boundTs vb wb t x false
        val res = if contained then SOME LESS else NONE
        val vb = add_var true x vb
      in
        (vb, wb +++ var_weight, res)
      end
  | tckbo below_lam boundTs vb wb (s as App (f, sTs, ss)) (FluidOrVar y) =
      let
        val (vb, wb, contained) = mfyVWBc below_lam boundTs vb wb s y true
        val res = if contained then SOME GREATER else NONE
        val vb = add_term false y vb
      in
        (vb, wb --- var_weight, res)
      end
    (* FIXME: don't ignore types *)
  | tckbo below_lam boundTs vb wb (App (f, _, ss)) (App (g, _, ts)) =
      let
        val (vb, wb, lex) = tckbo' below_lam boundTs vb wb f g ([](*FIXME*), ss) ([](*FIXME*), ts)
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
and tckbo' below_lam boundTs vb wb f g (_, ss) (_, ts) =
      if is_equal (prec_ord (f, g))
        then tckbolex (below_lam orelse f = Lam) boundTs vb wb ([](*FIXME*), ss) ([](*FIXME*), ts)
        else
          let
            val (vb, wb) = mfyVWB_tl (below_lam orelse f = Lam) boundTs vb wb ([](*FIXME*), ss) true
            val (vb, wb) = mfyVWB_tl (below_lam orelse g = Lam) boundTs vb wb ([](*FIXME*), ts) false
          in
            (vb, wb, NONE)
          end
    (* FIXME: don't ignore types *)
and tckbolex below_lam boundTs vb wb (_, []) (_, []) = (vb, wb, SOME EQUAL)
  | tckbolex below_lam boundTs vb wb (_, s :: ss) (_, t :: ts) =
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
          then tckbolex below_lam boundTs vb wb ([](*FIXME*), ss) ([](*FIXME*), ts)
          else
            let
              val (vb, wb) = mfyVWB_tl below_lam boundTs vb wb ([](*FIXME*), ss) true
              val (vb, wb) = mfyVWB_tl below_lam boundTs vb wb ([](*FIXME*), ts) false
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

end;