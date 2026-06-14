signature KBO_TERM =
sig

  (* FIXME: get rid of boundTs *)
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
  include SLAM_WEIGHT
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
open Slam_Weight
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
  val weight_of : T -> Slam_Order.weight
  val add_weight : bool -> Slam_Order.weight -> T -> T 
  val swap : T -> T
end;

structure Weight_Balance_Pure : WEIGHT_BALANCE =
struct

open Slam_Weight

type T = { weight: weight, swapped: bool } 

val empty = { weight = Slam_Order.zero_weight, swapped = false }

fun weight_of { weight = weight, swapped = swapped } = (swapped ? Slam_Weight.negate) weight

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

(* FIXME: BROKEN *)
structure Weight_Balance_Ref : WEIGHT_BALANCE =
struct

open Slam_Weight

type T = Weight_Balance_Pure.T Unsynchronized.ref

val empty = Unsynchronized.ref Weight_Balance_Pure.empty

fun weight_of r = Weight_Balance_Pure.weight_of (!r)

fun add_weight x y r = let val () = Unsynchronized.change r (Weight_Balance_Pure.add_weight x y) in r end

fun swap r = let val () = Unsynchronized.change r Weight_Balance_Pure.swap in r end

end

structure Weight_Balance: WEIGHT_BALANCE = Weight_Balance_Pure

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

signature SLAM_KBO =
sig

  (* terms *)
  
  include KBO_TERM
 
  datatype kbo_view
    = FluidOrVar of kbo_term 
    | App of fo_head * typ list * kbo_term list

  val view_of : kbo_term -> kbo_view

  (* Löchner - 2007 - Things to Know when Implementing KBO *)

  type kbo_data_ref = kbo_data Unsynchronized.ref

  val weight : kbo_data -> Slam_Weight.weight

  val empty : kbo_data

  val swap_ref : kbo_data_ref -> unit
  
  val map_var_ref : kbo_data_ref -> (Term_Balance.T -> Term_Balance.T) -> unit
  val map_tvar_ref : kbo_data_ref -> (Typ_Balance.T -> Typ_Balance.T) -> unit
  val map_weight_ref : kbo_data_ref -> (Weight_Balance.T -> Weight_Balance.T) -> unit

  val add_var_ref : kbo_data_ref -> bool -> KBOTermTab.key -> unit

  val add_weight_ref : kbo_data_ref -> bool -> Slam_Order.weight -> unit

  val T_mfyVWBc_ref :
    kbo_data_ref -> typ -> (* TVar *) (indexname * sort) option -> bool -> bool option
  val T_mfyVWBc_tl_ref :
    kbo_data_ref -> typ list -> (* TVar *) (indexname * sort) option -> bool -> bool option

  val mfyVWBc_ref :
    kbo_data_ref -> kbo_view -> (* variable *) kbo_term option -> bool -> bool option
  val mfyVWBc_tl_ref :
    kbo_data_ref -> kbo_view list -> (* variable *) kbo_term option -> bool -> bool option

  val T_tckbo_ref : kbo_data_ref -> typ -> typ -> Slam_Order.partial_order
  val T_tckbo'_ref :
    kbo_data_ref
    -> typ (* Type *)
    -> typ (* Type *)
    -> Slam_Order.partial_order
  val T_tckbolex_ref : kbo_data_ref -> typ list -> typ list -> Slam_Order.partial_order

  val tckbo_ref : kbo_data_ref -> kbo_view -> kbo_view -> Slam_Order.partial_order
  val tckbo'_ref :
    kbo_data_ref
    -> kbo_view (* App *)
    -> kbo_view (* App *)
    -> Slam_Order.partial_order
  val tckbolex_ref : kbo_data_ref -> kbo_view list -> kbo_view list -> Slam_Order.partial_order

  (* ''a is either indexname or string *)
  val eq_tvar_tfree : (''a * sort) -> (''a * sort) -> bool
  val eq_fluid_or_var : kbo_term -> kbo_term -> bool

  val ord : term * term -> Slam_Order.partial_order
end;

structure Slam_KBO : SLAM_KBO =
struct

fun drop_snd_none (x, NONE) = x
  | drop_snd_none _ = error "drop_snd_none: got SOME"

open KBO_Term

fun eq_tvar_tfree (x_name, x_sort) (y_name, y_sort) =
  x_name = y_name andalso
    (Type.eq_sort (Sign.tsig_of @{theory}) (x_sort, y_sort) orelse
      error ("same name but different sorts:" ^
        @{make_string} (x_name, x_sort) ^ " and " ^ @{make_string} (y_name, y_sort)))

fun eq_fluid_or_var
  { boundTs = x_boundTs, below_lam = x_below_lam, term = x_term }
  { boundTs = y_boundTs, below_lam = y_below_lam, term = y_term }
=
  x_below_lam = y_below_lam andalso x_term aconv y_term

open Slam_Weight

fun arity Lam = error "arity not defined for Lam"
  | arity (Fun (_, ar, _)) = ar

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

type kbo_data_ref = kbo_data Unsynchronized.ref

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

fun swap_ref r = Unsynchronized.change r swap

fun map_var f { var = var, tvar = tvar, weight = weight } =
  { var = f var, tvar = tvar, weight = weight }

fun map_var_ref r = Unsynchronized.change r o map_var

fun map_tvar f { var = var, tvar = tvar, weight = weight } =
  { var = var, tvar = f tvar, weight = weight }

fun map_tvar_ref r = Unsynchronized.change r o map_tvar
  
fun map_weight f { var = var, tvar = tvar, weight = weight } =
  { var = var, tvar = tvar, weight = f weight }

fun map_weight_ref r = Unsynchronized.change r o map_weight

fun add_var increment x = map_var (Term_Balance.add_var increment x)

fun add_var_ref r = Unsynchronized.change r oo add_var

fun add_weight increment weight =
  map_weight (Weight_Balance.add_weight increment weight)

fun add_weight_ref r = Unsynchronized.change r oo add_weight

fun T_mfyVWBc_ref kbo_data (x as TVar (x_name, x_sort)) y increment =
      let
        val () = map_tvar_ref kbo_data (Typ_Balance.add_var increment x)
        val () = add_weight_ref kbo_data increment KBO_Config.var_weight
      in
        Option.map (eq_tvar_tfree (x_name, x_sort)) y
      end
  | T_mfyVWBc_ref kbo_data (TFree (name, sort)) y increment =
      let
        val () = add_weight_ref kbo_data increment (KBO_Config.weight_of_type_constructor name)
      in
        Option.map (K false) y
      end
  | T_mfyVWBc_ref kbo_data (Type (name, args)) y increment =
      let
        val res = T_mfyVWBc_tl_ref kbo_data args y increment
        val () = add_weight_ref kbo_data increment (KBO_Config.weight_of_type_constructor name)
      in res end

and T_mfyVWBc_tl_ref kbo_data [] y _ = Option.map (K false) y
  | T_mfyVWBc_tl_ref kbo_data (s :: ss) y increment =
      let
        val y_in_s = T_mfyVWBc_ref kbo_data s y increment
        val () = \<^assert> (is_some y_in_s = is_some y)
      in
        case y_in_s of
          NONE => let val () = T_mfyVWB_tl_ref kbo_data ss increment in NONE end (* shortcut, don't care *)
        | SOME true => let val () = T_mfyVWB_tl_ref kbo_data ss increment in y_in_s end (* shortcut, already know *)
        | SOME false => T_mfyVWBc_tl_ref kbo_data ss y increment (* keep checking *)
      end

and T_mfyVWB_tl_ref kbo_data ss increment =
  case T_mfyVWBc_tl_ref kbo_data ss NONE increment of NONE => () | SOME _ => error "got SOME"
  

(* val mfyVWBc : kbo_data -> kbo_term -> kbo_term (* variable *) -> bool -> kbo_data * bool *)
fun mfyVWBc_ref kbo_data (FluidOrVar x) y increment =
      let
        val () = add_var_ref kbo_data increment x
        val () = add_weight_ref kbo_data increment KBO_Config.var_weight
      in
        Option.map (eq_fluid_or_var x) y
      end
  | mfyVWBc_ref kbo_data (App (f, ssT, ss)) y increment =
      let
        val () = T_mfyVWB_tl_ref kbo_data ssT increment
        val res = mfyVWBc_tl_ref kbo_data (map view_of ss) y increment
        val () = add_weight_ref kbo_data increment (KBO_Config.weight_of_fo_head f)
      in res end

and mfyVWBc_tl_ref kbo_data [] y _ = Option.map (K false) y
  | mfyVWBc_tl_ref kbo_data (s :: ss) y increment =
      let
        val y_in_s = mfyVWBc_ref kbo_data s y increment
        val () = \<^assert> (is_some y_in_s = is_some y)
      in
        case y_in_s of
          NONE => let val () = mfyVWB_tl_ref kbo_data ss increment in NONE end (* shortcut, don't care *)
        | SOME true => let val () = mfyVWB_tl_ref kbo_data ss increment in y_in_s end (* shortcut, already know *)
        | SOME false => mfyVWBc_tl_ref kbo_data ss y increment (* keep checking *)
      end

and mfyVWB_tl_ref kbo_data ss increment =
  case mfyVWBc_tl_ref kbo_data ss NONE increment of NONE => () | SOME _ => error "got SOME"

fun T_tckbo_ref kbo_data (x as TVar x_data) (y as TVar y_data) =
      let
        val () = map_tvar_ref kbo_data (Typ_Balance.add_var true x)
        val () = map_tvar_ref kbo_data (Typ_Balance.add_var false y)
      in
        if eq_tvar_tfree x_data y_data then SOME EQUAL else NONE
      end

  (* TFree, Type (the difference matters only to T_mfyVWBc) *)
  | T_tckbo_ref kbo_data (TVar x) t =
      let
        val SOME x_in_t = T_mfyVWBc_ref kbo_data t (SOME x) false
        val () = map_tvar_ref kbo_data (Typ_Balance.add_var true (TVar x))
        val () = add_weight_ref kbo_data true (KBO_Config.weight_of_tfree_or_type_constructor t)
      in
        if x_in_t then SOME LESS else NONE
      end

  | T_tckbo_ref kbo_data (TFree (a_name, a_sort)) (TFree (b_name, b_sort)) =
      (* T_tckbo kbo_data (Type (a_name, [])) (Type (b_name, [])) *)
      let
        val lex =
          (* result of tckbo' with two empty lists as arguments *)
          if eq_tvar_tfree (a_name, a_sort) (b_name, b_sort)
            then SOME EQUAL
            else NONE
        val () = add_weight_ref kbo_data true (KBO_Config.weight_of_tfree a_name)
        val () = add_weight_ref kbo_data false (KBO_Config.weight_of_tfree b_name)
        val GREATER_or_NONE = if Typ_Balance.no_neg (#tvar (!kbo_data)) then SOME GREATER else NONE
        val LESS_or_NONE = if Typ_Balance.no_pos (#tvar (!kbo_data)) then SOME LESS else NONE
        val res =
          (case Slam_Order.weight_ord (weight (!kbo_data), Slam_Order.zero_weight) of
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
        res
      end

  | T_tckbo_ref kbo_data (TFree (a_name, a_sort)) (Type (f, ts)) =
      let 
        val () = T_mfyVWB_tl_ref kbo_data ts false (* result of tckbo' with f \<noteq> g *) 
        val () = add_weight_ref kbo_data true (KBO_Config.weight_of_tfree a_name)
        val () = add_weight_ref kbo_data false (KBO_Config.weight_of_type_constructor f)
        val GREATER_or_NONE = if Typ_Balance.no_neg (#tvar (!kbo_data)) then SOME GREATER else NONE
        val LESS_or_NONE = if Typ_Balance.no_pos (#tvar (!kbo_data)) then SOME LESS else NONE
        val res =
          (case Slam_Order.weight_ord (weight (!kbo_data), Slam_Order.zero_weight) of
              GREATER => GREATER_or_NONE
            | LESS => LESS_or_NONE
            | EQUAL =>
                (* Type > TFree, thus g > f *) 
                LESS_or_NONE)
      in
        res
      end

  | T_tckbo_ref kbo_data (s as Type (f, ss)) (t as Type (g, ts)) =
      let
        val lex = T_tckbo'_ref kbo_data s t 
        val () = add_weight_ref kbo_data true (KBO_Config.weight_of_type_constructor f)
        val () = add_weight_ref kbo_data false (KBO_Config.weight_of_type_constructor g)
        val GREATER_or_NONE = if Typ_Balance.no_neg (#tvar (!kbo_data)) then SOME GREATER else NONE
        val LESS_or_NONE = if Typ_Balance.no_pos (#tvar (!kbo_data)) then SOME LESS else NONE
        val res =
          (case Slam_Order.weight_ord (weight (!kbo_data), Slam_Order.zero_weight) of
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
        res
      end

  (* TFree - TVar, Type - TVar, Type - TFree *) 
  | T_tckbo_ref kbo_data s t =
      let
        val () = swap_ref kbo_data
        val res = T_tckbo_ref kbo_data t s
        val () = swap_ref kbo_data
      in
        Slam_Common.map_some rev_order res
      end

and T_tckbo'_ref kbo_data (Type (f, ss)) (Type (g, ts)) =
  if f = g
    then T_tckbolex_ref kbo_data ss ts
    else
      let
        val () = T_mfyVWB_tl_ref kbo_data ss true
        val () = T_mfyVWB_tl_ref kbo_data ts false
      in
        NONE
      end

and T_tckbolex_ref kbo_data [] [] = SOME EQUAL
  | T_tckbolex_ref kbo_data (s :: ss) (t :: ts) =
      let
        val res = T_tckbo_ref kbo_data s t 
      in
        if res = SOME EQUAL
          then T_tckbolex_ref kbo_data ss ts
          else
            let
              val () = T_mfyVWB_tl_ref kbo_data ss true
              val () = T_mfyVWB_tl_ref kbo_data ts false
            in
              res
            end
      end

fun tckbo_ref kbo_data (x as FluidOrVar x_data) (y as FluidOrVar y_data) =
  let
    val () = map_var_ref kbo_data (Term_Balance.add_var true x_data)
    val () = map_var_ref kbo_data (Term_Balance.add_var false y_data)
  in
    if eq_fluid_or_var x_data y_data then SOME EQUAL else NONE 
  end

  | tckbo_ref kbo_data (FluidOrVar x) (t as App (f, _, _)) =
      let
        val SOME x_in_t = mfyVWBc_ref kbo_data t (SOME x) false
        val () = map_var_ref kbo_data (Term_Balance.add_var true x)
        val () = add_weight_ref kbo_data true (KBO_Config.weight_of_fo_head f)
      in
        if x_in_t then SOME LESS else NONE
      end

  | tckbo_ref kbo_data (s as App (f, _, _)) (t as App (g, _, _)) =
      let
        val lex = tckbo'_ref kbo_data s t
        val () = add_weight_ref kbo_data true (KBO_Config.weight_of_fo_head f) (* + \<phi>(f) *)
        val () = add_weight_ref kbo_data false (KBO_Config.weight_of_fo_head g) (* - \<phi>(g) *)
        val GREATER_or_NONE = if Term_Balance.no_neg (#var (!kbo_data)) then SOME GREATER else NONE
        val LESS_or_NONE = if Term_Balance.no_pos (#var (!kbo_data)) then SOME LESS else NONE
        val res =
          (case Slam_Order.weight_ord (weight (!kbo_data), Slam_Order.zero_weight) of
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
        res
      end
  
  (* App - FluidOrVar *)
  | tckbo_ref kbo_data s t =
      let
        val () = swap_ref kbo_data
        val res = tckbo_ref kbo_data t s
        val () = swap_ref kbo_data
      in
        Slam_Common.map_some rev_order res
      end

and tckbo'_ref kbo_data (App (f, ssT, ss)) (App (g, tsT, ts)) =
  if f = g (* FIXME: is this logically equivalent to equality under the precendence order? *)
    then
      (case T_tckbolex_ref kbo_data ssT tsT of
        (* FIXME: check all other places where we call T_... variants and make sure that we sequence
        the type and term kbo correctly. Or factor out a mixed tckbolex which takes all four lists. *)
        SOME EQUAL => tckbolex_ref kbo_data (map view_of ss) (map view_of ts)
      | res =>
          let
            val () = mfyVWB_tl_ref kbo_data (map view_of ss) true
            val () = mfyVWB_tl_ref kbo_data (map view_of ts) false
          in
            res
          end)
    else
      let
        val () = T_mfyVWB_tl_ref kbo_data ssT true
        val () = T_mfyVWB_tl_ref kbo_data tsT false
        val () =   mfyVWB_tl_ref kbo_data (map view_of ss) true
        val () =   mfyVWB_tl_ref kbo_data (map view_of ts) false
      in
        NONE
      end

and tckbolex_ref kbo_data [] [] = SOME EQUAL
  | tckbolex_ref kbo_data (s :: ss) (t :: ts) =
      let
        val res = tckbo_ref kbo_data s t (* FIXME: move the view_of calls here *)
      in
        if res = SOME EQUAL
          then tckbolex_ref kbo_data ss ts
          else
            let
              val () = mfyVWB_tl_ref kbo_data ss true
              val () =  mfyVWB_tl_ref kbo_data ts false
            in
              res 
            end
      end

fun ord_ref (s, t) =
  let
    val kbo_data = Unsynchronized.ref empty
  in
    tckbo_ref kbo_data (view_of (to_kbo_term s)) (view_of (to_kbo_term t))
  end

val ord = ord_ref 

end;
