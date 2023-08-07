(* reference implementation of KBO *)

signature JEHA_ORDER_REFERENCE =
sig
  (* copy pasted *)
  type partial_order = order option
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

  type fo_term
  val mk_de_bruijn_constant : int -> typ -> term
  val translate_O : term -> fo_term
  val translate_P : fo_term -> fo_term
  val translate_p : fo_term -> fo_term
  val to_fo_term : term -> fo_term
  val pretty_fo_term : Proof.context -> fo_term -> string
  val fo_head_weight : string -> weight
  val fo_term_weight : fo_term -> weight
  val fold_fo_vars : (term * bool -> 'a -> 'a) -> fo_term -> 'a -> 'a
  val fo_var_counts : fo_term -> int Termtab.table * int Termtab.table
  val fo_kbo_greater_equal : (fo_term * fo_term) -> bool
end;

structure Jeha_Order_Reference: JEHA_ORDER_REFERENCE =
struct

(* copy pasted *)
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



(* Translation *)

(* db\<^sup>i *)
fun mk_de_bruijn_constant level T = Const ("jehakboolambdasupdebruijn" ^ @{make_string} level, T)

fun mk_fo_const_name (Const (name, _)) = "Const" ^ name
  | mk_fo_const_name (Free (name, _)) = "Free" ^ name
  | mk_fo_const_name _ = error "invalid input for mk_fo_const_name"

datatype fo_head =
  (* term.ML typ *)
  FOType of string * typ list (* Type *)
| FOTFree of string * sort (* *)
  (* term.ML: term *)
| FOConst of string * typ (* Const without \<forall>, \<exists> *)
| FOForall (* HOL.All *)
| FOExists (* HOL.Ex *)
| FOFree of string * typ
| FOLam
(* Below lambda *)
| FOForallPrime
| FOExistsPrime
| FODeBruijn of int

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
  FOApp of string * fo_term list
  (* includes type variables via dummy_pattern *)
  (* first arg is a fluid term or a Var or a dummy_pattern with a TVar with dummy sort as type *)
| FOVar of term * bool (* z\<^sub>t, z\<^sub>t' with false, true resp. *)

(* name apart terms and types, i.e. Const, Free, Var, Type, TFree, TVar by
prefixing constructor names *)
fun type_to_fo_term (Type (name, Ts)) = FOApp ("Type" ^ name, map type_to_fo_term Ts)
  | type_to_fo_term (TFree (name, _)) = FOApp ("TFree" ^ name, [])
  (* TVar encoded as Const ("Pure.dummy_pattern", T) with sort replaced by dummy sort [""] *)
  | type_to_fo_term (TVar (name, _)) = FOVar (Term.dummy_pattern (TVar (name, Term.dummyS)), false)

fun is_Abs (Abs _) = true
  | is_Abs _ = false

fun is_Comb (_ $ _) = true
  | is_Comb _ = false

(* B\<^sub>x from the \<lambda>oSup Paper
replace one Bound by the constant *)
fun translate_O_bound level T (t as (Bound i)) =
      if level = i then mk_de_bruijn_constant level T else t
  | translate_O_bound level T (s $ t) =
      translate_O_bound level T s $ translate_O_bound level T t
  | translate_O_bound level T (Abs (x, S, u)) = Abs (x, S, translate_O_bound (level + 1) T u)
  | translate_O_bound _ _ t = t

(* O from the \<lambda>oSup Paper *)
fun translate_O t =
  if JTerm.might_be_fluid t orelse is_Var t
    then FOVar (t, false)
  else if is_Abs t then
    translate_O_Abs t
  else
    (* all other cases are treated as applications, strip_comb behaves correctly *)
    let val (head, args) = strip_comb t in
      if (not (JTerm.is_quantifier head)) orelse length args = 0
        then FOApp (mk_fo_const_name head, type_to_fo_term (fastype_of head) :: map translate_O args)
        else translate_O_Quant t
    end
and translate_O_Abs (Abs (_, T, u)) =
  FOApp ("Lam", [type_to_fo_term T, translate_O (translate_O_bound 0 T u)])
(* argument is an Abs because of Q\<^sub>\<eta> normal form *)
and translate_O_Quant (quantifier $ (Abs (_, T, u))) =
  FOApp (mk_fo_const_name quantifier, [type_to_fo_term T, translate_O (translate_O_bound 0 T u)])

fun translate_p (t as FOVar (Const ("Pure.dummy_pattern", _), _)) = t (* \<alpha> *)
  | translate_p (FOVar (t, false)) = FOVar (t, true)
  | translate_p (FOVar (t, true)) = error "fresh var encountered in translate_p"
  | translate_p (FOApp (f, ts)) =
      FOApp (
        if (f = "ConstHOL.All" orelse f = "ConstHOL.Ex") andalso length ts = 2
          then "Prime" ^ f
          else f
        ,
        map translate_p ts
      )

fun translate_P (FOVar t) = FOVar t (* \<alpha> and z\<^sub>u *)
  | translate_P (t as FOApp (f, ts)) =
      if String.isPrefix "Lam" f
        then let val [T, u] = ts in FOApp (f, [T, translate_p u]) end
      else if String.isPrefix "Type" f
                orelse String.isPrefix "TFree" f
                orelse String.isPrefix "Const" f
                orelse String.isPrefix "Free" f
        then FOApp (f, map translate_P ts)
        else error ("translate_P: fo function symbol can't be " ^ f)

val to_fo_term = translate_P o translate_O

fun pretty_fo_term ctxt (FOVar (t, below_lam)) = Jeha_Common.pretty_term ctxt t ^ (if below_lam then "'" else "")
  | pretty_fo_term ctxt (FOApp (f, ts)) =
      if length ts = 0
        then f ^ "0"
        else f ^ @{make_string} (length ts - 1) ^ "(" ^ space_implode ", " (map (pretty_fo_term ctxt) ts) ^ ")"



(* KBO reference implementation *)

fun fo_head_weight f =
  if String.isPrefix "Constjehakboolambdasupdebruijn" f
    then bound_weight
  else if String.isPrefix "Var" f orelse String.isPrefix "TVar" f
    then var_weight
  else if String.isPrefix "ConstHOL.All" f orelse String.isPrefix "Const.HOL.Ex" f
    then quantifier_weight false
  else if String.isPrefix "Prime" f
    then quantifier_weight true
  else if exists (fn p => String.isPrefix p f) ["Const", "Free", "Type", "TFree"]
    then const_weight
  else if String.isPrefix "Lam" f
    then fo_lambda_weight
  else error ("fo_head_weight: fo function symbol can't be " ^ f)

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

fun fo_kbo_greater_equal (s as (FOApp (f, ss)), (t as FOApp (g, ts))) =
      counts_greater_equal (fo_var_counts s) (fo_var_counts t)
      andalso (
        fo_term_weight s > fo_term_weight t
        orelse fo_term_weight_s = fo_term_weight t andalso error "implement prec on strings"
        orelse fo_term_weight_s = fo_term_weight t andalso error "implement fo kbo lex"
      )
      error ""
      (* \<forall> x \<in> t. |s|\<^sub>x \<ge> |t|\<^sub>x*)
      (* \<phi>(s) \<ge> \<phi>(t) *)
      (* *)
  | fo_kbo_greater_equal (FOApp (f, ss), FOVar x) =
      error ""

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

end;