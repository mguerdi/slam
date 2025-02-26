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

signature BALANCE =
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

functor Balance(Tab : TABLE) : BALANCE =
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

structure Term_Balance = Balance(Termtab);
structure Typ_Balance = Balance(Typtab);

signature JEHA_KBO =
sig

  (* terms *)
 
  type kbo_term = { boundTs : typ list, below_lam : bool, term : term }

  val to_kbo_term : term -> kbo_term

  datatype fo_head
    = Lam
    | Fun of term (* ignore type information *) * int

  datatype kbo_view
    = FluidOrVar of term * bool
    | App of fo_head * typ list * kbo_term list

  val view_of : kbo_term -> kbo_view

  (* Löchner - 2007 - Things to Know when Implementing KBO *)

  type kbo_data =
    { var : Term_Balance.T
    , var_below_lam : Term_Balance.T
    , tvar : Typ_Balance.T
    , weight : Weight_Balance.T
    }

  val weight : kbo_data -> Jeha_Weight.weight

  val empty : kbo_data
  
  val swap : kbo_data -> kbo_data

  val map_var : (Term_Balance.T -> Term_Balance.T) -> kbo_data -> kbo_data
  val map_var_below_lam : (Term_Balance.T -> Term_Balance.T) -> kbo_data -> kbo_data
  val map_tvar : (Typ_Balance.T -> Typ_Balance.T) -> kbo_data -> kbo_data
  val map_weight : (Weight_Balance.T -> Weight_Balance.T) -> kbo_data -> kbo_data

  val add_weight : bool -> Jeha_Order.weight -> kbo_data -> kbo_data

  val T_mfyVWBc : kbo_data -> typ -> (* TVar *) (indexname * sort) -> bool -> kbo_data * bool
  val T_mfyVWBc_tl : kbo_data -> typ list -> (* TVar *) (indexname * sort) -> bool -> kbo_data * bool

  val mfyVWBc : kbo_data -> kbo_term -> kbo_term (* variable *) -> bool -> kbo_data * bool
  val mfyVWBc_tl : kbo_data -> kbo_term list -> kbo_term (* variable *) -> bool -> kbo_data * bool

  val T_tckbo : kbo_data -> typ -> typ -> kbo_data * Jeha_Order.partial_order
  val T_tckbo' :
    kbo_data
    -> typ
    -> typ
    -> kbo_data * Jeha_Order.partial_order
  val T_tckbolex : kbo_data -> typ list -> typ list -> kbo_data * Jeha_Order.partial_order

  val tckbo : kbo_data -> kbo_term -> kbo_term -> kbo_data * Jeha_Order.partial_order
  val tckbo' :
    kbo_data
    -> fo_head -> typ list -> kbo_term list
    -> fo_head -> typ list -> kbo_term list
    -> kbo_data * Jeha_Order.partial_order
  val tckbolex : kbo_data -> kbo_term list -> kbo_term list -> kbo_data * Jeha_Order.partial_order
  
  (* ''a is either indexname or string *)
  val eq_tvar_tfree : (''a * sort) -> (''a * sort) -> bool
end;

structure Jeha_Kbo : JEHA_KBO =
struct

fun eq_tvar_tfree (x_name, x_sort) (y_name, y_sort) =
  x_name = y_name andalso
    (Type.eq_sort (Sign.tsig_of @{theory}) (x_sort, y_sort) orelse
      error ("same name but different sorts:" ^
        @{make_string} (x_name, x_sort) ^ " and " ^ @{make_string} (y_name, y_sort)))

open Jeha_Weight

type kbo_term = { boundTs : typ list, below_lam : bool, term : term }

fun to_kbo_term t = { boundTs = [], below_lam = false, term = t }

datatype fo_head
  = Lam
  | Fun of term (* ignore type information *) * int

fun arity Lam = error "arity not defined for Lam"
  | arity (Fun (_, ar)) = ar

datatype kbo_view
  = FluidOrVar of term * bool
  | App of fo_head * typ list * kbo_term list

(* incremental translation to first order term *)
(* Idea: implement on-the-fly versions of mfyVWBc that don't rely on this translation. *)
fun view_of { below_lam = below_lam, term = (t as (Var _)), ... } = FluidOrVar (t, below_lam)
  | view_of { term = (t as (Free (_, T))), ... } = App (Fun (t, 0), [T], [])
  | view_of { term = (t as (Const (_, T))), ... } = App (Fun (t, 0), [T], [])
  | view_of { boundTs = boundTs, term = (t as (Bound i)), ... } =
      App (Fun (t, 0), [nth boundTs i], [])
  | view_of { below_lam = below_lam, boundTs = boundTs, term = t } =
      if JTerm.might_be_fluid t
        then FluidOrVar (t, below_lam)
        else
          (case t of
            Abs (_, T, u) => App (Lam, [T], [{ boundTs = T::boundTs, below_lam = true, term = u }])
          | (_ $ _) =>
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
                App (Fun (f, length ts), [T], ts)
              end)

type kbo_data =
  { var : Term_Balance.T
  , var_below_lam : Term_Balance.T
  , tvar : Typ_Balance.T
  , weight : Weight_Balance.T 
  }

val weight = Weight_Balance.weight_of o #weight

val empty =
  { var = Term_Balance.empty
  , var_below_lam = Term_Balance.empty
  , tvar = Typ_Balance.empty
  , weight = Weight_Balance.empty
  }

fun swap { var = var, var_below_lam = var_below_lam, tvar = tvar, weight = weight } =
  { var = Term_Balance.swap var
  , var_below_lam = Term_Balance.swap var_below_lam
  , tvar = Typ_Balance.swap tvar
  , weight = Weight_Balance.swap weight
  }

fun map_var f { var = var, var_below_lam = var_below_lam, tvar = tvar, weight = weight } =
  { var = f var, var_below_lam = var_below_lam, tvar = tvar, weight = weight }
  
fun map_var_below_lam f { var = var, var_below_lam = var_below_lam, tvar = tvar, weight = weight } =
  { var = var, var_below_lam = f var_below_lam, tvar = tvar, weight = weight }
  
fun map_tvar f { var = var, var_below_lam = var_below_lam, tvar = tvar, weight = weight } =
  { var = var, var_below_lam = var_below_lam, tvar = f tvar, weight = weight }
  
fun map_weight f { var = var, var_below_lam = var_below_lam, tvar = tvar, weight = weight } =
  { var = var, var_below_lam = var_below_lam, tvar = tvar, weight = f weight }

fun add_weight increment weight =
  map_weight (Weight_Balance.add_weight increment weight)

fun T_mfyVWBc kbo_data (x as (TVar (x_name, x_sort))) (y_name, y_sort) increment =
      ( kbo_data
        |> map_tvar (Typ_Balance.add_var increment x)
        |> add_weight increment (Jeha_Order.var_weight)
      , eq_tvar_tfree (x_name, x_sort) (y_name, y_sort)
      )
  | T_mfyVWBc kbo_data (TFree (name, sort)) (y_name, y_sort) increment =
      ( kbo_data
        |> add_weight increment (Jeha_Order.weight_of_type_constructor name)
      , false
      )
  | T_mfyVWBc kbo_data (Type (name, args)) (y_name, y_sort) increment =
      kbo_data
      |> (fn d => T_mfyVWBc_tl d args (y_name, y_sort) increment)
      |>> add_weight increment (Jeha_Order.weight_of_type_constructor name)

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
fun mfyVWBc kbo_data x y increment = error "mfyVWBc unimplemented"

and mfyVWBc_tl kbo_data [] y increment = error "mfyVWBc_tl unimplemented"
  | mfyVWBc_tl kbo_data (s :: ss) y increment = error "mfyVWBc_tl unimplemented"

fun T_tckbo kbo_data (x as (TVar x_data)) (y as (TVar y_data)) : kbo_data * Jeha_Order.partial_order =
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
      |>> add_weight true (Jeha_Order.weight_of_tfree_or_type_constructor t)
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
          |> add_weight true (Jeha_Order.weight_of_tfree a_name)
          |> add_weight false (Jeha_Order.weight_of_tfree b_name)
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
          |> add_weight true (Jeha_Order.weight_of_tfree a_name)
          |> add_weight false (Jeha_Order.weight_of_type_constructor f)
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

  | T_tckbo kbo_data (s as (Type (f, ss))) (t as (Type (g, ts))) =
      let
        val (kbo_data, lex) =
          T_tckbo' kbo_data s t 
          |>> add_weight true (Jeha_Order.weight_of_type_constructor f)
          |>> add_weight false (Jeha_Order.weight_of_type_constructor g)
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

fun tckbo kbo_data f g = error "tckbo unimplemented"

and tckbo' kbo_data f ssT ss g tsT ts = error "tckbo' unimplemented"

and tckbolex kbo_data [] [] = error "tckbolex unimplemented"
  | tckbolex kbo_data (s :: ss) (t :: ts) = error "tckbolex unimplemented"

end;