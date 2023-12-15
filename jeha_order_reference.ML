(* reference implementation of KBO *)

signature JEHA_ORDER_REFERENCE =
sig
  type partial_order = order option
  (* copy pasted *)
  type weight = int * int
  val plus_weight : weight -> weight -> weight
  val weight_ord : weight ord
  val var_weight : weight
  val const_weight : weight
  val quantifier_weight : bool -> weight
  val bound_weight : weight
  val fo_lambda_weight : weight
  (* for reference *)
  val type_weight : typ -> weight
  val term_weight : bool -> term -> weight

  type fo_head
  type fo_term
  val translate_O : typ list -> term -> fo_term
  val translate_P : fo_term -> fo_term
  val translate_p : fo_term -> fo_term
  val to_fo_term : term -> fo_term
  val pretty_fo_term : Proof.context -> fo_term -> string
  val fo_head_weight : fo_head -> weight
  val fo_term_weight : fo_term -> weight
  val fold_fo_vars : (term * bool -> 'a -> 'a) -> fo_term -> 'a -> 'a
  val fo_var_counts : fo_term -> int Termtab.table * int Termtab.table
  val fo_prec_greater : (fo_head * int) * (fo_head * int) -> bool
  val lex_greater : (''a * ''a -> bool) -> (''a list * ''a list) -> bool
  val fo_kbo_greater : (fo_term * fo_term) -> bool

  val kbo : (term * term) -> partial_order
end;

structure Jeha_Order_Reference: JEHA_ORDER_REFERENCE =
struct

type partial_order = order option

(* copy pasted *)
infix 6 +++
infix 6 ---

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



(* Translation *)

datatype fo_head =
  (* term.ML typ *)
  FOType of string (* Type *)
| FOTFree of string * sort (* *)
  (* term.ML: term *)
  (* FIXME: same name but different type are different? *)
| FOConst of string * typ (* Const without \<forall>, \<exists> *)
| FOForall (* HOL.All *)
| FOExists (* HOL.Ex *)
| FOFree of string * typ
| FOLam
(* Below lambda *)
| FOForallPrime
| FOExistsPrime
| FODeBruijn of int

fun mk_fo_const_head (Const ("HOL.All", _)) = FOForall
  | mk_fo_const_head (Const ("HOL.Ex", _)) = FOExists
  | mk_fo_const_head (Bound i) = FODeBruijn i
  | mk_fo_const_head (Const c) = FOConst c
  | mk_fo_const_head (Free c) = FOFree c
  | mk_fo_const_head _ = error "invalid input for mk_fo_const_head"

fun type_of_head Ts (Bound i) = nth Ts i
  | type_of_head _ t = fastype_of t

datatype fo_term =
  (* the first element of the list is the type of the bound var in case of
  quantifiers and lambdas and the type of the function symbol otherwise *)
  (* the string is either of
  Lam
  Prime...
  Const...
  Constjehakboolambdasupdebruijn...
  Free...
  Type...
  TFree...
  *)
  FOApp of fo_head * fo_term list
  (* includes type variables via dummy_pattern *)
  (* first arg is a fluid term or a Var or a dummy_pattern with a TVar with dummy sort as type *)
| FOVar of term * bool (* z\<^sub>t, z\<^sub>t' with false, true resp. *)

fun type_to_fo_term (Type (name, Ts)) = FOApp (FOType name, map type_to_fo_term Ts)
  | type_to_fo_term (TFree (name, Ss)) = FOApp (FOTFree (name, Ss), [])
  (* TVar encoded as Const ("Pure.dummy_pattern", T) with sort replaced by dummy sort [""] *)
  | type_to_fo_term (TVar (name, _)) = FOVar (Term.dummy_pattern (TVar (name, Term.dummyS)), false)

fun is_Abs (Abs _) = true
  | is_Abs _ = false

fun is_Comb (_ $ _) = true
  | is_Comb _ = false

(*
(* B\<^sub>x from the \<lambda>oSup Paper
replace one Bound by the constant *)
fun translate_O_bound level T (t as (Bound i)) =
      if level = i then mk_de_bruijn_constant level T else t
  | translate_O_bound level T (s $ t) =
      translate_O_bound level T s $ translate_O_bound level T t
  | translate_O_bound level T (Abs (x, S, u)) = Abs (x, S, translate_O_bound (level + 1) T u)
  | translate_O_bound _ _ t = t
*)

(* O from the \<lambda>oSup Paper *)
fun translate_O Ts t =
  if JTerm.might_be_fluid t orelse is_Var t
    then FOVar (t, false)
  else if is_Abs t then
    translate_O_Abs Ts t
  else
    (* all other cases are treated as applications, strip_comb behaves correctly *)
    let val (head, args) = strip_comb t in
      if (not (JTerm.is_quantifier head)) orelse length args = 0
        then FOApp (mk_fo_const_head head, type_to_fo_term (type_of_head Ts head) :: map (translate_O Ts) args)
        else translate_O_Quant Ts t
    end
and translate_O_Abs Ts (Abs (_, T, u)) =
  FOApp (FOLam, [type_to_fo_term T, translate_O (T::Ts) u])
(* argument is an Abs because of Q\<^sub>\<eta> normal form *)
and translate_O_Quant Ts (quantifier $ (Abs (_, T, u))) =
  FOApp (mk_fo_const_head quantifier, [type_to_fo_term T, translate_O (T::Ts) u])
  | translate_O_Quant Ts t = error ("translate_O_Quant: wrong normal form" ^ @{make_string} t)

fun translate_p (t as FOVar (Const ("Pure.dummy_pattern", _), _)) = t (* \<alpha> *)
  | translate_p (FOVar (t, false)) = FOVar (t, true)
  | translate_p (FOVar (t, true)) = error "fresh var encountered in translate_p"
  | translate_p (FOApp (f, ts)) =
      FOApp (
        if f = FOForall andalso length ts = 2
          then FOForallPrime
        else if f = FOExists andalso length ts = 2
          then FOExistsPrime
        else f
        ,
        map translate_p ts
      )

(* NOTE: Testing Idea: when doing translation on the fly, make it a kind of fold that is generic
over the "operation that sits on the bottom". Then create an operation, which just "reads off" the
first-order term and compare that to the explicit translation.

Simple example:
(* the explicit "translation" *)
val vars_below_lambda : term -> term list
(* the generic fold which supplies information on the fly *)
val fold_aterm' : ('a -> { below_lam : bool } -> term -> 'a) -> 'a -> term -> 'a
(* *)
val read_off : term list -> { below_lam : bool } -> term -> term list
(* the test case *)
ALL t. vars_below_lambda t = fold_aterm' read_off [] t

The challenge is adapting this to a a simultaneous traversal of two terms and making sure we don't
carry too much useless information around in the generic fold, just to be able to write the test.
Although we could always "compile" that extra information out by hand once we're happy that it
works. *) 



fun translate_P (FOVar t) = FOVar t (* \<alpha> and z\<^sub>u *)
  | translate_P (t as FOApp (FOLam, [T, u])) = FOApp (FOLam, [T, translate_p u])
  | translate_P (FOApp (f, ts)) = FOApp (f, map translate_P ts)

val to_fo_term = translate_P o translate_O []

fun pretty_fo_head ctxt (FOType name) = "Type-" ^ name
  | pretty_fo_head ctxt (FOTFree (name, S)) = "TFree-" ^ name ^ "-" ^ "sort?"
  | pretty_fo_head ctxt (FOConst (name, T)) = "Const-" ^ name ^ "-" ^ Jeha_Common.pretty_typ ctxt T
  | pretty_fo_head ctxt FOForall = "\<forall>"
  | pretty_fo_head ctxt FOExists = "\<exists>"
  | pretty_fo_head ctxt (FOFree (name, T)) = "Free-" ^ name ^ "-" ^ Jeha_Common.pretty_typ ctxt T
  | pretty_fo_head ctxt FOLam = "\<lambda>"
  | pretty_fo_head ctxt FOForallPrime = "\<forall>'"
  | pretty_fo_head ctxt FOExistsPrime = "\<exists>'"
  | pretty_fo_head ctxt (FODeBruijn level) = "db_" ^ @{make_string} level


fun pretty_fo_term ctxt (FOVar (t, below_lam)) = Jeha_Common.pretty_term ctxt t ^ (if below_lam then "'" else "")
  | pretty_fo_term ctxt (FOApp (f, ts)) =
      if length ts = 0
        then pretty_fo_head ctxt f (* ^ "0" *)
        else pretty_fo_head ctxt f (* ^ @{make_string} (length ts - 1) *) ^ "(" ^ space_implode ", " (map (pretty_fo_term ctxt) ts) ^ ")"



(* KBO reference implementation *)

fun fo_head_weight (FODeBruijn _) = bound_weight
  | fo_head_weight FOForall = quantifier_weight false
  | fo_head_weight FOExists = quantifier_weight false
  | fo_head_weight FOForallPrime = quantifier_weight true
  | fo_head_weight FOExistsPrime = quantifier_weight true
  | fo_head_weight (FOType _) = const_weight
  | fo_head_weight (FOTFree _) = const_weight
  | fo_head_weight (FOConst _) = const_weight
  | fo_head_weight (FOFree _) = const_weight
  | fo_head_weight Lam = fo_lambda_weight

(* FIXME: test against HOL based reference above *)
fun fo_term_weight (FOVar _) = var_weight
  | fo_term_weight (FOApp (f, ts)) =
      fo_head_weight f +++ fold (curry (op +++)) (map fo_term_weight ts) zero_weight

fun fold_fo_vars f (FOVar x) acc = f x acc
  | fold_fo_vars f (FOApp (_, ts)) acc = fold (fold_fo_vars f) ts acc

fun fo_var_counts t =
  let
    fun add_var v = Termtab.map_default (v, 0) (fn n => n + 1)
    fun add_tagged_var (v, below_lam) (above_counts, below_counts) =
      if below_lam
        then (above_counts, add_var v below_counts)
        else (add_var v above_counts, below_counts)
  in
    fold_fo_vars add_tagged_var t (Termtab.empty, Termtab.empty)
  end

fun counts_greater_equal ((s_counts_above, s_counts_below), (t_counts_above, t_counts_below)) =
  let
    fun single_counts_greater_equal counts1 counts2 =
      (* forall in counts2, need counts1 geq *)
      Termtab.fold (fn (t, count) => fn acc => acc andalso the_default 0 (Termtab.lookup counts1 t) >= count) counts2 true
  in
    single_counts_greater_equal s_counts_above t_counts_above
    andalso single_counts_greater_equal s_counts_below t_counts_below
  end

(* lam > db > quantifier > symbols > bot > top *)
fun prec_key FOLam = 11
  | prec_key (FODeBruijn _) = 10
  | prec_key FOForall = 9
  | prec_key FOExists = 8
  | prec_key FOForallPrime = 7
  | prec_key FOExistsPrime = 6
  | prec_key (FOConst (@{const_name "HOL.False"}, _)) = 3
  | prec_key (FOConst (@{const_name "HOL.True"}, _)) = 2
  | prec_key (FOConst _) = 5
  | prec_key (FOFree _) = 4
  (* these shouldn't ever be compared against the others *)
  | prec_key (FOType _) = 1
  | prec_key (FOTFree _) = 0

(* compare De Bruijn to De Bruijn, Const to Const, etc. *)
fun fo_prec_same_class_ord (FODeBruijn i, FODeBruijn j) = int_ord (i, j)
    (* FIXME: types? *)
  | fo_prec_same_class_ord (FOConst (s, _), FOConst (t, _)) = string_ord (s, t)
  | fo_prec_same_class_ord (FOFree (s, _), FOFree (t, _)) = string_ord (s, t)
  | fo_prec_same_class_ord (FOType s, FOType t) = string_ord (s, t)
  | fo_prec_same_class_ord (FOTFree (s, _), FOTFree (t, _)) = string_ord (s, t)
  | fo_prec_same_class_ord (s, t) =
        if s <> t then
          error ("fo_prec_same_class_ord: not the same constructors?" ^
            @{make_string} s ^ " and " ^ @{make_string} t)
        else
          EQUAL

(* coarse grained, then fine grained if equal *)
val fo_prec_symbol_ord = apply2 prec_key #> int_ord ||| fo_prec_same_class_ord

(* val fo_prec_ord = apply2 #1 #> fo_prec_symbol_ord ||| apply2 #2 #> int_ord  *)
val fo_prec_ord = prod_ord fo_prec_symbol_ord int_ord

fun fo_prec_greater st = GREATER = fo_prec_ord st

fun lex_greater a_ord ([], []) = false
  | lex_greater a_ord (s::ss, t::ts) =
      (* FIXME: appropriate equality? *)
      if s = t
        then lex_greater a_ord (ss, ts)
        else a_ord (s, t)
  | lex_greater _ _ = error "unequal number of args in lexicographic comparison"

(* Things to know when implementing KBO, Definition 1 *)
fun fo_kbo_greater (s as (FOApp (f, ss)), (t as FOApp (g, ts))) =
      (* Need to take below_lam into account in recursive call *)
      counts_greater_equal (fo_var_counts s, fo_var_counts t) (* 1 *)
      andalso (
        GREATER = weight_ord (fo_term_weight s, fo_term_weight t) (* 2a *)
        orelse (
          fo_term_weight s = fo_term_weight t (* 2b or 2c *)
          andalso (
            fo_prec_greater ((f, length ss), (g, length ts)) (* 2b *)
            orelse (f = g andalso lex_greater fo_kbo_greater (ss, ts)) (* 2c *)
          )
        )
      )
  | fo_kbo_greater (s as (FOApp _), t as FOVar _) =
      counts_greater_equal (fo_var_counts s, fo_var_counts t)
  | fo_kbo_greater _ = false




(*
KBO only compares args if heads are equal

*)

(* Issues:
* sorts are ignored
  Questions:
  * how do sorts behave under substitution?
  * do we compare sorts? (very possible)
* overloaded constants
*)

(*
Testable properties

* invariant w.r.t. aconv
* (O1) - (O4)
* t = s => not t > s
* strictness: t > s => not s > t
* injectivity by constructing a reverse translation

*)

fun kbo (t, s) =
  let
    val t_eq_s = t aconv s
    val (fo_t, fo_s) = apply2 to_fo_term (t, s)
    val t_g_s = fo_kbo_greater (fo_t, fo_s)
    val t_l_s = fo_kbo_greater (fo_s, fo_t)
  in
    if t_eq_s
      then if t_g_s
        then error "Reference KBO: eq and greater"
      else if t_l_s
        then error "Reference KBO: eq and less"
      else SOME EQUAL
    else if t_g_s
      then if t_l_s
        then error "Reference KBO: greater and less"
      else SOME GREATER
    else if t_l_s
      then SOME LESS
    else
      NONE
  end

end;