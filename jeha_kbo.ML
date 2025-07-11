signature KBO_TERM =
sig

  type kbo_term = { boundTs : typ list, below_lam : bool, term : term }

  val to_kbo_term : term -> kbo_term

  datatype fo_head
    = Lam
    | Fun of term (* ignore type information *) * int * bool

end;

structure KBO_Term : KBO_TERM =
struct

type kbo_term = { boundTs : typ list, below_lam : bool, term : term }

fun to_kbo_term t = { boundTs = [], below_lam = false, term = t }

datatype fo_head
  = Lam
  | Fun of term (* ignore type information *) * int * bool

end;

signature KBO_CONFIG =
sig
  include JEHA_WEIGHT
  include KBO_TERM
  val var_weight : weight
  val const_weight : weight
  val weight_of_type_constructor : string -> weight
  val weight_of_tfree : string -> weight
  val weight_of_tfree_or_type_constructor : typ -> weight
  val weight_of_fo_head : fo_head -> weight
  val quantifier_weight : bool -> weight
  
  (* debugging *)
  val prec_key_fun : term -> bool (* below_lam *) -> int
  val prec_key : fo_head -> int
  
  val fo_head_precedence_ord : fo_head ord
end;

structure KBO_Config : KBO_CONFIG =
struct
open Jeha_Weight
open KBO_Term

val var_weight = (0, 1)
val const_weight = (0, 1)

fun weight_of_type_constructor _ = const_weight
fun weight_of_tfree _ = const_weight
fun weight_of_tfree_or_type_constructor (TFree (name, _)) = weight_of_tfree name
  | weight_of_tfree_or_type_constructor (Type (name, _)) = weight_of_type_constructor name

(* below lambdas there are only \<forall>' and \<exists>' *)
fun quantifier_weight below_lam = if below_lam then const_weight else (1, 0)

fun weight_of_fo_head _ = const_weight

fun prec_key_fun (Bound _) _ = 10
  | prec_key_fun (Const (@{const_name HOL.All}, _)) false = 9
  | prec_key_fun (Const (@{const_name HOL.Ex}, _)) false = 8
  | prec_key_fun (Const (@{const_name HOL.All}, _)) true = 7
  | prec_key_fun (Const (@{const_name HOL.Ex}, _)) true = 6
  | prec_key_fun (Const (@{const_name HOL.False}, _)) _ = 3
  | prec_key_fun (Const (@{const_name HOL.True}, _)) _ = 2
  | prec_key_fun (Const _) _ = 5
  | prec_key_fun (Free _) _ = 4
  | prec_key_fun t _ = error ("prec_key_fun: " ^ @{make_string} t ^ " can't be a head")

fun prec_key Lam = 11
  | prec_key (Fun (f, _, below_lam)) = prec_key_fun f below_lam

fun prec_same_class_ord (Fun (Bound i, _, _), Fun (Bound j, _, _)) = int_ord (i, j) 
  | prec_same_class_ord (Fun (Const (s, _), _, _), Fun (Const (t, _), _, _)) = string_ord (s, t)
  | prec_same_class_ord (Fun (Free (s, _), _, _), Fun (Free (t, _), _, _)) = string_ord (s, t)
  | prec_same_class_ord (Lam, Lam) = EQUAL
  | prec_same_class_ord (s, t) =
      error ("prec_same_class_ord: can't be heads: " ^
        @{make_string} s ^ " and " ^ @{make_string} t)

fun arity_ord (Fun (_, f_ar, _), Fun (_, g_ar, _)) = int_ord (f_ar, g_ar) 
  | arity_ord (Lam, Lam) = EQUAL
  | arity_ord _ = error "arity_ord: attempt to compare arity of Fun and Lam"

val fo_head_precedence_ord = apply2 prec_key #> int_ord ||| prec_same_class_ord ||| arity_ord

end;

signature WEIGHT_BALANCE =
sig
  type T
  val empty : T
  val weight_of : T -> Jeha_Order.weight
  val add_weight : bool -> Jeha_Order.weight -> T -> T 
  val swap : T -> T
end;

structure Weight_Balance : WEIGHT_BALANCE =
struct

open Jeha_Weight

type T = { weight: weight, swapped: bool } 

val empty = { weight = Jeha_Order.zero_weight, swapped = false }

fun weight_of { weight = weight, swapped = swapped } = (swapped ? Jeha_Weight.negate) weight

fun add_weight increment added_weight { weight = weight, swapped = swapped } =
  let
    val actually_increment = (swapped ? not) increment
  in
    if actually_increment
      then { weight = weight +++ added_weight, swapped = swapped }
      else { weight = weight --- added_weight, swapped = swapped }
  end

fun swap { weight = weight, swapped = swapped } = { weight = weight, swapped = not swapped }

end;

signature VAR_BALANCE =
sig
  type key
  type table
  type T
  val empty : T
  (* val map_balances : (table -> table) -> T -> T
  val map_pos_counter : (int -> int) -> T -> T
  val map_neg_counter : (int -> int) -> T -> T *)
  (* negate balances on the fly *)
  val swap : T -> T
  val add_var : bool -> key -> T -> T
  val no_pos : T -> bool
  val no_neg : T -> bool
end;

functor Var_Balance(Tab : TABLE) : VAR_BALANCE =
struct

type key = Tab.key

type table = int Tab.table

type T = { balances: table, pos_balances: int, neg_balances: int, swapped: bool }

val empty = { balances = Tab.empty, pos_balances = 0, neg_balances = 0, swapped = false }

fun map_balances f balance =
  { balances = f (#balances balance)
  , pos_balances = #pos_balances balance
  , neg_balances = #neg_balances balance
  , swapped = #swapped balance
  }

fun map_pos_counter f balance =
  { balances = #balances balance
  , pos_balances = f (#pos_balances balance)
  , neg_balances = #neg_balances balance
  , swapped = #swapped balance
  }

fun map_neg_counter f balance =
  { balances = #balances balance
  , pos_balances = #pos_balances balance
  , neg_balances = f (#neg_balances balance)
  , swapped = #swapped balance
  }

fun swap balance =
  { balances = #balances balance
  , pos_balances = #pos_balances balance
  , neg_balances = #neg_balances balance
  , swapped = not (#swapped balance)
  }

fun add_var (increment : bool) (var : key) balance =
  let
    val increment = (#swapped balance ? not) increment (* FIXME: is this enough? *)
    val new_balances =
      #balances balance |> Tab.map_default (var, 0) (curry (op +) (if increment then 1 else ~1))
    val new_count = the (Tab.lookup new_balances var)
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

fun no_pos { pos_balances = pos_balances, neg_balances = neg_balances, swapped = swapped, ... } =
  if swapped
    then neg_balances = 0
    else pos_balances = 0

fun no_neg { pos_balances = pos_balances, neg_balances = neg_balances, swapped = swapped, ... } =
  if swapped
    then pos_balances = 0
    else neg_balances = 0

end;

structure KBOTermKey : KEY = 
struct

type key = KBO_Term.kbo_term 

fun ord
  ( { boundTs = x_boundTs, below_lam = x_below_lam, term = x_term }
  , { boundTs = y_boundTs, below_lam = y_below_lam, term = y_term }
  )
=
  (case bool_ord (x_below_lam, y_below_lam) of EQUAL =>
    (let
      fun open_ord smallestFree tu =
        if pointer_eq tu then EQUAL else
        (case tu of
          (Abs (_, T, t), Abs (_, U, u)) =>
            (case Term_Ord.typ_ord (T, U) of EQUAL => open_ord (smallestFree + 1) (t, u) | r => r)
        | (t1 $ t2, u1 $ u2) =>
            (case open_ord smallestFree (t1, t2) of EQUAL => open_ord smallestFree (u1, u2) | r => r)
        | (Bound i, Bound j) =>
            (case int_ord (i, j) of
              (* FIXME: cache the results of this comparison for each loose bound var *)
              EQUAL =>
                if i < smallestFree (* bound *)
                  then EQUAL 
                  else
                    Term_Ord.typ_ord
                      (nth x_boundTs (i - smallestFree), nth y_boundTs (j - smallestFree))
            | r => r)
        | _ => Term_Ord.fast_term_ord tu)
    in
      open_ord 0 (x_term, y_term)
    end)
  | r => r)

end

structure KBOTermTab = Table(KBOTermKey)

structure Term_Balance = Var_Balance(KBOTermTab);
(* FIXME: Consider an indexname * sort key (the argument of TVar) so it becomes more similar to
Term_Balance *)
structure Typ_Balance = Var_Balance(Typtab);

signature JEHA_KBO =
sig

  (* terms *)
  
  include KBO_TERM
 
  datatype kbo_view
    = FluidOrVar of kbo_term 
    | App of fo_head * typ list * kbo_term list

  val view_of : kbo_term -> kbo_view

  (* Löchner - 2007 - Things to Know when Implementing KBO *)

  type kbo_data =
    { var : Term_Balance.T
    , tvar : Typ_Balance.T
    , weight : Weight_Balance.T
    }

  val weight : kbo_data -> Jeha_Weight.weight

  val empty : kbo_data

  val swap : kbo_data -> kbo_data

  val map_var : (Term_Balance.T -> Term_Balance.T) -> kbo_data -> kbo_data
  val map_tvar : (Typ_Balance.T -> Typ_Balance.T) -> kbo_data -> kbo_data
  val map_weight : (Weight_Balance.T -> Weight_Balance.T) -> kbo_data -> kbo_data

  val add_var : bool -> KBOTermTab.key -> kbo_data -> kbo_data

  val add_weight : bool -> Jeha_Order.weight -> kbo_data -> kbo_data

  (* FIXME: Consider having (indexname * sort) option for the variable to indicate whether we're
  doing mfyVWBc or mfyVWB. *)
  val T_mfyVWBc : kbo_data -> typ -> (* TVar *) (indexname * sort) -> bool -> kbo_data * bool
  val T_mfyVWBc_tl : kbo_data -> typ list -> (* TVar *) (indexname * sort) -> bool -> kbo_data * bool

  val mfyVWBc : kbo_data -> kbo_view -> kbo_view (* variable *) -> bool -> kbo_data * bool
  val mfyVWBc_tl : kbo_data -> kbo_view list -> kbo_view (* variable *) -> bool -> kbo_data * bool

  val T_tckbo : kbo_data -> typ -> typ -> kbo_data * Jeha_Order.partial_order
  val T_tckbo' :
    kbo_data
    -> typ (* Type *)
    -> typ (* Type *)
    -> kbo_data * Jeha_Order.partial_order
  val T_tckbolex : kbo_data -> typ list -> typ list -> kbo_data * Jeha_Order.partial_order

  val tckbo : kbo_data -> kbo_view -> kbo_view -> kbo_data * Jeha_Order.partial_order
  val tckbo' :
    kbo_data
    -> kbo_view (* App *)
    -> kbo_view (* App *)
    -> kbo_data * Jeha_Order.partial_order
  val tckbolex : kbo_data -> kbo_view list -> kbo_view list -> kbo_data * Jeha_Order.partial_order

  (* ''a is either indexname or string *)
  val eq_tvar_tfree : (''a * sort) -> (''a * sort) -> bool
  val eq_fluid_or_var : kbo_term -> kbo_term -> bool
  
  val ord : term * term -> Jeha_Order.partial_order
end;

structure Jeha_KBO : JEHA_KBO =
struct

open KBO_Term

fun eq_tvar_tfree (x_name, x_sort) (y_name, y_sort) =
  x_name = y_name andalso
    (Type.eq_sort (Sign.tsig_of @{theory}) (x_sort, y_sort) orelse
      error ("same name but different sorts:" ^
        @{make_string} (x_name, x_sort) ^ " and " ^ @{make_string} (y_name, y_sort)))

(* based on aconv from term.ML, compare KBOTermKey.ord *)
fun aconv_bound smallestFree boundTs1 tm1 boundTs2 tm2 =
  pointer_eq (tm1, tm2) orelse
    (case (tm1, tm2) of
      (t1 $ u1, t2 $ u2) =>
        aconv_bound smallestFree boundTs1 t1 boundTs2 t2
          andalso aconv_bound smallestFree boundTs1 u1 boundTs2 u2
    | (Abs (_, T1, t1), Abs (_, T2, t2)) =>
        aconv_bound (smallestFree + 1) boundTs1 t1 boundTs2 t2 andalso T1 = T2
    | (Bound i, Bound j) =>
        i = j andalso
          (i < smallestFree (* bound *)
            (* FIXME: cache the results of this comparison for each loose bound var *)
            orelse nth boundTs1 (i - smallestFree) = nth boundTs2 (j - smallestFree))
    | (a1, a2) => a1 = a2);

(* aconv is not sufficent, we need aconv in a bound context *)
fun eq_fluid_or_var
  { boundTs = x_boundTs, below_lam = x_below_lam, term = x_term }
  { boundTs = y_boundTs, below_lam = y_below_lam, term = y_term }
=
  x_below_lam = y_below_lam andalso aconv_bound 0 x_boundTs x_term y_boundTs y_term

open Jeha_Weight

fun arity Lam = error "arity not defined for Lam"
  | arity (Fun (_, ar, _)) = ar

(* Question

f :: 'a \<Rightarrow> 'b

\<lambda> x :: 'a \<Rightarrow> 'b. f ?
f (\<lambda> x :: 'a \<Rightarrow> 'b. )

lam('a \<Rightarrow> 'b, f(?))
f('a \<Rightarrow> 'b, lam(?))

long story short: Is it possible for two Fluid terms to be compared which differ only by the type of
a bound variable?

YESYESYES

Example:

The variable check has a fluid term as a var, and the left term contains an instance of the same
fluid term which differs only in the type of a bound variable!

var = ?y db\<^sup>0 (in bound context ['a])
term = \<lambda>x::'b. ?y db\<^sup>0

first-order term = lam('b, ?y db\<^sup>0)

But the var does not occur in the term!

Aside:
  Can the opposite happen? E.g. should db\<^sup>0 and db\<^sup>1 ever be considered the same term?

  The term order does not allow this but maybe allowing this would be an improvement?

Another "fine point":
  It's not enough to just compare the bound environments as well, what matters are the types of the
  bound variables that actuallly appear in the respective fluid terms.

It's kind of weird to consider fluid terms in different bound contexts to be the same variable.

Research: duper just compares using ==, zipperposition uses Term.equal.

Anyways - conlcusion:

When comparing fluid terms, the types of bound variables need to be taken into account.

*)

datatype kbo_view
  = FluidOrVar of kbo_term 
  | App of fo_head * typ list * kbo_term list

(* incremental translation to first order term *)
(* Idea: implement on-the-fly versions of mfyVWBc that don't rely on this translation. *)
fun view_of { below_lam = below_lam, term = t as Var _, ... } =
      FluidOrVar { boundTs = [], below_lam = below_lam, term = t }
  | view_of { below_lam = below_lam, boundTs = boundTs, term = t as Abs (_, T, u) } =
      if JTerm.might_be_fluid t
        then FluidOrVar { boundTs = boundTs, below_lam = below_lam, term = t }
        else App (Lam, [T], [{ boundTs = T::boundTs, below_lam = true, term = u }])
  | view_of { below_lam = below_lam, boundTs = boundTs, term = t as _ $ _ } =
      if JTerm.might_be_fluid t
        then FluidOrVar { boundTs = boundTs, below_lam = below_lam, term = t }
        else
          let
            val (f, ts) = strip_comb t
            val T = fastype_of1 (boundTs, f)
            val (T, ts) =
              if JTerm.is_quantifier f
                (* The FO type argument of a quantifier is the binder type, not the type of the
                quantifier, similarly the fo term argument is the lambdas body, not the lambda. *)
                then
                  let val [Abs(_, T, u)] = ts in
                    (T, [{boundTs = T::boundTs, below_lam = below_lam, term = u}])
                  end
                (* Note: below quantifier does not mean below lambda! *)
                else (T, map (fn t => { boundTs = boundTs, below_lam = below_lam, term = t }) ts)
          in
            App (Fun (f, length ts, below_lam), [T], ts)
          end
  (* Const, Free, Bound *)
  | view_of { boundTs = boundTs, term = t, below_lam = below_lam } =
      let
        val T = fastype_of1 (boundTs, t)
      in
        App (Fun (t, 0, below_lam), [T], [])
      end

type kbo_data =
  { var : Term_Balance.T
  , tvar : Typ_Balance.T
  , weight : Weight_Balance.T 
  }

val weight = Weight_Balance.weight_of o #weight

val empty =
  { var = Term_Balance.empty
  , tvar = Typ_Balance.empty
  , weight = Weight_Balance.empty
  }

fun swap { var = var, tvar = tvar, weight = weight } =
  { var = Term_Balance.swap var
  , tvar = Typ_Balance.swap tvar
  , weight = Weight_Balance.swap weight
  }

fun map_var f { var = var, tvar = tvar, weight = weight } =
  { var = f var, tvar = tvar, weight = weight }
  
fun map_tvar f { var = var, tvar = tvar, weight = weight } =
  { var = var, tvar = f tvar, weight = weight }
  
fun map_weight f { var = var, tvar = tvar, weight = weight } =
  { var = var, tvar = tvar, weight = f weight }

fun add_var increment x = map_var (Term_Balance.add_var increment x)

fun add_weight increment weight =
  map_weight (Weight_Balance.add_weight increment weight)

fun T_mfyVWBc kbo_data (x as TVar (x_name, x_sort)) (y_name, y_sort) increment =
      ( kbo_data
        |> map_tvar (Typ_Balance.add_var increment x)
        |> add_weight increment KBO_Config.var_weight
      , eq_tvar_tfree (x_name, x_sort) (y_name, y_sort)
      )
  | T_mfyVWBc kbo_data (TFree (name, sort)) (y_name, y_sort) increment =
      ( kbo_data
        |> add_weight increment (KBO_Config.weight_of_type_constructor name)
      , false
      )
  | T_mfyVWBc kbo_data (Type (name, args)) (y_name, y_sort) increment =
      kbo_data
      |> (fn d => T_mfyVWBc_tl d args (y_name, y_sort) increment)
      |>> add_weight increment (KBO_Config.weight_of_type_constructor name)

and T_mfyVWBc_tl kbo_data [] y increment = (kbo_data, false)
  | T_mfyVWBc_tl kbo_data (s :: ss) y increment =
      let
        val (kbo_data, res) = T_mfyVWBc kbo_data s y increment
      in
        if not res
          then T_mfyVWBc_tl kbo_data ss y increment
          else (T_mfyVWB_tl kbo_data ss increment, true)
      end

(* #1 o T_mfyVWBc_tl = T_mfyVWB_tl *)
and T_mfyVWB_tl kbo_data ss increment =
  #1 (T_mfyVWBc_tl kbo_data ss (("", ~1), dummyS) increment)

(* val mfyVWBc : kbo_data -> kbo_term -> kbo_term (* variable *) -> bool -> kbo_data * bool *)
fun mfyVWBc kbo_data (FluidOrVar x) (FluidOrVar y) increment =
      ( kbo_data
        |> add_var increment x
        |> add_weight increment KBO_Config.var_weight
      , eq_fluid_or_var x y
      )
  | mfyVWBc kbo_data (App (f, ssT, ss)) (FluidOrVar y) increment =
      kbo_data
      |> (fn d => T_mfyVWB_tl d ssT increment)
      |> (fn d => mfyVWBc_tl d (map view_of ss) (FluidOrVar y) increment)            
      |>> add_weight increment (KBO_Config.weight_of_fo_head f)

and mfyVWBc_tl kbo_data [] y increment = (kbo_data, false)
  | mfyVWBc_tl kbo_data (s :: ss) y increment =
      let
        val (kbo_data, res) = mfyVWBc kbo_data s y increment
      in
        if not res
          then mfyVWBc_tl kbo_data ss y increment
          else (mfyVWB_tl kbo_data ss increment, true)
      end

and mfyVWB_tl kbo_data ss increment =
  mfyVWBc_tl
    kbo_data
    ss
    (FluidOrVar { boundTs = [], below_lam = false, term = Var (("", ~1), dummyT) })
    increment
  |> #1

fun T_tckbo kbo_data (x as TVar x_data) (y as TVar y_data) =
      ( kbo_data
        |> map_tvar (Typ_Balance.add_var true x)
        |> map_tvar (Typ_Balance.add_var false y)
      , if eq_tvar_tfree x_data y_data then SOME EQUAL else NONE
      )

  (* TFree, Type (the difference matters only to T_mfyVWBc) *)
  | T_tckbo kbo_data (TVar x) t =
      kbo_data
      |> (fn d => T_mfyVWBc d t x false)
      |>> map_tvar (Typ_Balance.add_var true (TVar x))
      |>> add_weight true (KBO_Config.weight_of_tfree_or_type_constructor t)
      ||> (fn contained => if contained then SOME LESS else NONE)

  | T_tckbo kbo_data (TFree (a_name, a_sort)) (TFree (b_name, b_sort)) =
      (* T_tckbo kbo_data (Type (a_name, [])) (Type (b_name, [])) *)
      let
        val lex =
          (* result of tckbo' with two empty lists as arguments *)
          if eq_tvar_tfree (a_name, a_sort) (b_name, b_sort)
            then SOME EQUAL
            else NONE
        val kbo_data =
          kbo_data
          |> add_weight true (KBO_Config.weight_of_tfree a_name)
          |> add_weight false (KBO_Config.weight_of_tfree b_name)
        val GREATER_or_NONE = if Typ_Balance.no_neg (#tvar kbo_data) then SOME GREATER else NONE
        val LESS_or_NONE = if Typ_Balance.no_pos (#tvar kbo_data) then SOME LESS else NONE
        val res =
          (case Jeha_Order.weight_ord (weight kbo_data, Jeha_Order.zero_weight) of
              GREATER => GREATER_or_NONE
            | LESS => LESS_or_NONE
            | EQUAL =>
          (case string_ord (a_name, b_name) of (* FIXME: precedence for TFree *)
              GREATER => GREATER_or_NONE
            | LESS => LESS_or_NONE
            (* Leaving out the case f \<noteq> g because our precedence is a total order. *)
            | EQUAL =>
          (case lex of
              SOME EQUAL => SOME EQUAL
            | SOME GREATER => GREATER_or_NONE
            | SOME LESS => LESS_or_NONE
            | NONE => NONE)))
      in
        (kbo_data, res) 
      end

  | T_tckbo kbo_data (TFree (a_name, a_sort)) (Type (f, ts)) =
      let 
        val kbo_data =
          T_mfyVWB_tl kbo_data ts false (* result of tckbo' with f \<noteq> g *) 
          |> add_weight true (KBO_Config.weight_of_tfree a_name)
          |> add_weight false (KBO_Config.weight_of_type_constructor f)
        val GREATER_or_NONE = if Typ_Balance.no_neg (#tvar kbo_data) then SOME GREATER else NONE
        val LESS_or_NONE = if Typ_Balance.no_pos (#tvar kbo_data) then SOME LESS else NONE
        val res =
          (case Jeha_Order.weight_ord (weight kbo_data, Jeha_Order.zero_weight) of
              GREATER => GREATER_or_NONE
            | LESS => LESS_or_NONE
            | EQUAL =>
                (* Type > TFree, thus g > f *) 
                LESS_or_NONE)
      in
        (kbo_data, res)
      end

  | T_tckbo kbo_data (s as Type (f, ss)) (t as Type (g, ts)) =
      let
        val (kbo_data, lex) =
          T_tckbo' kbo_data s t 
          |>> add_weight true (KBO_Config.weight_of_type_constructor f)
          |>> add_weight false (KBO_Config.weight_of_type_constructor g)
        val GREATER_or_NONE = if Typ_Balance.no_neg (#tvar kbo_data) then SOME GREATER else NONE
        val LESS_or_NONE = if Typ_Balance.no_pos (#tvar kbo_data) then SOME LESS else NONE
        val res =
          (case Jeha_Order.weight_ord (weight kbo_data, Jeha_Order.zero_weight) of
              GREATER => GREATER_or_NONE
            | LESS => LESS_or_NONE
            | EQUAL =>
          (case string_ord (f, g) of (* FIXME: precedence for Type *)
              GREATER => GREATER_or_NONE
            | LESS => LESS_or_NONE
            (* Leaving out the case f \<noteq> g because our precedence is a total order. *)
            | EQUAL =>
          (case lex of
              SOME EQUAL => SOME EQUAL
            | SOME GREATER => GREATER_or_NONE
            | SOME LESS => LESS_or_NONE
            | NONE => NONE)))
      in
        (kbo_data, res) 
      end

  (* TFree - TVar, Type - TVar, Type - TFree *) 
  | T_tckbo kbo_data s t =
      let
        val (kbo_data, res) = T_tckbo (swap kbo_data) t s
      in
        (swap kbo_data, Jeha_Common.map_some rev_order res)
      end

and T_tckbo' kbo_data (Type (f, ss)) (Type (g, ts)) =
  if f = g
    then T_tckbolex kbo_data ss ts
    else
      ( kbo_data
        |> (fn d => T_mfyVWB_tl d ss true)
        |> (fn d => T_mfyVWB_tl d ts false)
      , NONE
      )

and T_tckbolex kbo_data [] [] = (kbo_data, SOME EQUAL)
  | T_tckbolex kbo_data (s :: ss) (t :: ts) =
      let
        val (kbo_data, res) = T_tckbo kbo_data s t 
      in
        if res = SOME EQUAL
          then T_tckbolex kbo_data ss ts
          else
            ( kbo_data
              |> (fn d => T_mfyVWB_tl d ss true)
              |> (fn d => T_mfyVWB_tl d ts false)
            , res
            )
      end

fun tckbo kbo_data (x as FluidOrVar x_data) (y as FluidOrVar y_data) =
  ( kbo_data
    |> map_var (Term_Balance.add_var true x_data)
    |> map_var (Term_Balance.add_var false y_data)
  , if eq_fluid_or_var x_data y_data then SOME EQUAL else NONE 
  )

  | tckbo kbo_data (x as FluidOrVar x_data) (t as App (f, _, _)) =
      kbo_data
      |> (fn d => mfyVWBc d t x false)
      |>> map_var (Term_Balance.add_var true x_data)
      |>> add_weight true (KBO_Config.weight_of_fo_head f)
      ||> (fn contained => if contained then SOME LESS else NONE)

  | tckbo kbo_data (s as App (f, _, _)) (t as App (g, _, _)) =
      let
        val (kbo_data, lex) =
          tckbo' kbo_data s t
          |>> add_weight true (KBO_Config.weight_of_fo_head f) (* + \<phi>(f) *)
          |>> add_weight false (KBO_Config.weight_of_fo_head g) (* - \<phi>(g) *)
        val GREATER_or_NONE = if Term_Balance.no_neg (#var kbo_data) then SOME GREATER else NONE
        val LESS_or_NONE = if Term_Balance.no_pos (#var kbo_data) then SOME LESS else NONE
        val res =
          (case Jeha_Order.weight_ord (weight kbo_data, Jeha_Order.zero_weight) of
              GREATER => GREATER_or_NONE
            | LESS => LESS_or_NONE
            | EQUAL =>
          (case KBO_Config.fo_head_precedence_ord (f, g) of
              GREATER => GREATER_or_NONE
            | LESS => LESS_or_NONE
            (* Leaving out the case f \<noteq> g because our precedence is a total order. *)
            | EQUAL =>
          (case lex of
              SOME EQUAL => SOME EQUAL
            | SOME GREATER => GREATER_or_NONE
            | SOME LESS => LESS_or_NONE
            | NONE => NONE)))
      in
        (kbo_data, res) 
      end
  
  (* App - FluidOrVar *)
  | tckbo kbo_data s t =
      let
        val (kbo_data, res) = tckbo (swap kbo_data) t s
      in
        (swap kbo_data, Jeha_Common.map_some rev_order res)
      end

and tckbo' kbo_data (App (f, ssT, ss)) (App (g, tsT, ts)) =
  if f = g (* FIXME: is this logically equivalent to equality under the precendence order? *)
    then
      (case T_tckbolex kbo_data ssT tsT of
        (* FIXME: check all other places where we call T_... variants and make sure that we sequence
        the type and term kbo correctly. Or factor out a mixed tckbolex which takes all four lists. *)
        (kbo_data, SOME EQUAL) => tckbolex kbo_data (map view_of ss) (map view_of ts)
      | (kbo_data, res) =>
          ( kbo_data
            |> (fn d => mfyVWB_tl d (map view_of ss) true)
            |> (fn d => mfyVWB_tl d (map view_of ts) false)
          , res
          ))
    else
      ( kbo_data
        |> (fn d => T_mfyVWB_tl d ssT true)
        |> (fn d => T_mfyVWB_tl d tsT false)
        |> (fn d => mfyVWB_tl d (map view_of ss) true)
        |> (fn d => mfyVWB_tl d (map view_of ts) false)
      , NONE
      )

and tckbolex kbo_data [] [] = (kbo_data, SOME EQUAL)
  | tckbolex kbo_data (s :: ss) (t :: ts) =
      let
        val (kbo_data, res) = tckbo kbo_data s t (* FIXME: move the view_of calls here *)
      in
        if res = SOME EQUAL
          then tckbolex kbo_data ss ts
          else
            ( kbo_data
              |> (fn d => mfyVWB_tl d ss true)
              |> (fn d => mfyVWB_tl d ts false)
            , res 
            )
      end

fun ord (s, t) = #2 (tckbo empty (view_of (to_kbo_term s)) (view_of (to_kbo_term t)))

end;