(* passive clause set and given clause heuristic *)

signature WEIGHT_FUNCTIONS =
sig
  type weight_fun = JClause.T -> int

  val combine: (weight_fun * int) list -> weight_fun

  val size_of_clause: weight_fun
  val number_of_distinct_vars: weight_fun
  val favor_small_num_vars: weight_fun
  val favor_all_ground_and_neg: weight_fun

  val favor_goal_symbols: Jeha_Symbol_Table.set -> weight_fun

  val default_fun: Jeha_Symbol_Table.set -> weight_fun
end

(* see zipperposition's clauseQueue.ml *)
structure Weight_Functions : WEIGHT_FUNCTIONS =
struct
  type weight_fun = JClause.T -> int

  val PENALTY_COEFF = 20

  (* FIXME: store a penalty in each clause (e.g. to penalize the descendants of certain inference
  rules *)

  fun combine weight_funs_and_coeffs clause =
    fold
      (fn (weight_fun, coeff) => fn acc => acc + coeff * weight_fun clause)
      weight_funs_and_coeffs
      0

  fun size_of_clause c =
    fold (fn (l, r, _) => fn acc => acc + size_of_term l + size_of_term r) (JClause.literals c) 0

  fun number_of_distinct_vars c =
    Vars.empty
    |> fold (fn (l, r, _) => Vars.add_vars l #> Vars.add_vars r) (JClause.literals c)
    |> Vars.size

  fun favor_small_num_vars c =
    let
      val n_vars = number_of_distinct_vars c
      val n =
        if n_vars < 4 then 0
        else if n_vars < 6 then 1
        else if n_vars < 8 then 3
        else n_vars
    in
      n * PENALTY_COEFF 
    end
    
  fun all_ground_and_neg c =
    forall (fn (lit as (l, r, _)) =>
      JLit.is_negative lit andalso JTerm.is_ground l andalso JTerm.is_ground r) (JClause.literals c)

  fun favor_all_ground_and_neg c = if all_ground_and_neg c then 0 else PENALTY_COEFF
  
  fun favor_positive_unit c = if JClause.is_positive_unit c then 0 else PENALTY_COEFF

  (* basic goal-oriented selection heuristic *)
  fun favor_goal_symbols goal_symbols c =
    let
      fun aterm_weight t =
        if Jeha_Symbol_Table.aterm_defined goal_symbols t then 0 else PENALTY_COEFF
      val add_term_weight = fold_aterms (fn t => fn acc => acc + aterm_weight t)
      val weight = fold (fn (l, r, _) => add_term_weight l #> add_term_weight r) (JClause.literals c) 0
    in
      weight
    end
  
  fun favor_free c =
    let
      fun aterm_weight (Free _) = 0 
        | aterm_weight _ = PENALTY_COEFF
      val add_term_weight = fold_aterms (fn t => fn acc => acc + aterm_weight t)
      val weight = fold (fn (l, r, _) => add_term_weight l #> add_term_weight r) (JClause.literals c) 0
    in
      weight
    end

  fun favor_initial c =
    case JClause.origin c of
      Jeha_Log.NegatedConjecture _ => 0
    | Jeha_Log.Axiom _ => 0
    | _ => PENALTY_COEFF

  (* tries to imitate zip's default_fun *)
  fun default_fun goal_symbols = combine
    [ (size_of_clause, 3)
    , (favor_all_ground_and_neg, 1)
    , (favor_small_num_vars, 1)
    , (favor_positive_unit, 1)
    (* FIXME: not the favor_goal from zip, which requires tracking distance to negated conjecture *)
    , (favor_goal_symbols goal_symbols, 1)
    , (favor_initial, 3)
    , (favor_free, 3)
    ]
end

signature JEHA_PASSIVE_SET =
sig
  type T 
  val init : Jeha_Symbol_Table.set -> JClause.T list -> T
  val seq_of : T -> JClause.T Seq.seq
  val add_new_clause : JClause.T -> T -> T 
  val add_new_clauses : T -> JClause.T list -> T 
  val select_given_clause : T -> JClause.T * T 
  val pretty : Proof.context -> int -> T -> string
  (* debug *)
  val length : T -> int
  structure Passive_Set : HEAP
end

structure Jeha_Passive_Set : JEHA_PASSIVE_SET =
struct

structure Passive_Set = Heap(type elem = int * JClause.T val ord = int_ord o apply2 fst)

type T = { heap: Passive_Set.T, weight: JClause.T -> int }

fun seq_of_heap heap =
  if Passive_Set.is_empty heap 
    then Seq.empty
    else Passive_Set.min_elem heap |>> snd ||> seq_of_heap |> uncurry Seq.cons

fun seq_of { heap, ... } = seq_of_heap heap

val length = seq_of #> Seq.list_of #> length

fun pretty_clauses_with_weight ctxt { weight, ... } (cs : JClause.T list) =
  cs
  |> map (fn c =>
    Pretty.block (
      Pretty.separate
        " "
        [JClause.pretty_clause' ctxt c, Pretty.str (" #=" ^ @{make_string} (weight c))]
     ))
  |> Pretty.commas
  |> Pretty.block
  |> Pretty.string_of
  
fun pretty ctxt n passive =
  let
    val first_n = passive |> seq_of |> Seq.take n |> Seq.list_of
  in
    ("passive [" ^ @{make_string} n ^ "/" ^ @{make_string} (length passive) ^ "]: ")
    ^ pretty_clauses_with_weight ctxt passive first_n
  end

(* initial clauses all have weight 0 so they are added to active set first *)
fun init goal_symbols clauses =
  let
    val weight = Weight_Functions.default_fun goal_symbols
  in
    { heap = fold Passive_Set.insert (map (op` weight) clauses) Passive_Set.empty
    , weight = weight
    }
  end

fun add_new_clause clause { heap, weight } =
  { heap = Passive_Set.insert (weight clause, clause) heap, weight = weight }

fun add_new_clauses passive clauses = fold add_new_clause clauses passive

fun select_given_clause { heap, weight } =
  let
    val (given_clause, heap) = Passive_Set.min_elem heap |>> snd
  in
    (given_clause, { heap = heap, weight = weight })
  end

end