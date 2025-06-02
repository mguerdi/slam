(* passive clause set and given clause heuristic *)

signature JEHA_PASSIVE_SET =
sig
  type T 
  val init : JClause.T list -> T
  val seq_of : T -> JClause.T Seq.seq
  val add_new_clause : JClause.T -> T -> T 
  val add_new_clauses : T -> JClause.T list -> T 
  val select_given_clause : T -> JClause.T * T 
  (* debug *)
  structure Passive_Set : HEAP
end

structure Jeha_Passive_Set : JEHA_PASSIVE_SET =
struct

fun size_of_clause c =
  fold (fn (l, r, _) => fn acc => acc + size_of_term l + size_of_term r) (JClause.literals c) 0

structure Passive_Set = Heap(type elem = int * JClause.T val ord = int_ord o apply2 fst)

type T = { heap: Passive_Set.T, weight: JClause.T -> int }

fun seq_of_heap heap =
  if Passive_Set.is_empty heap 
    then Seq.empty
    else Passive_Set.min_elem heap |>> snd ||> seq_of_heap |> uncurry Seq.cons

fun seq_of { heap, ... } = seq_of_heap heap

(* initial clauses all have weight 0 so they are added to active set first *)
fun init clauses =
  let
    (* FIXME: Goal-oriented selection heuristic *)
    fun weight clause = size_of_clause clause
  in
    (* FIXME: map (op` weight) clauses ? *)
    { heap = fold Passive_Set.insert (map (pair 0) clauses) Passive_Set.empty
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