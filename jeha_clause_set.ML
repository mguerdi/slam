signature JEHA_CLAUSE_SET =
sig
  type T
  val empty : T
  val add_new_clause : JClause.T -> T -> T
  val add_new_clauses : JClause.T list -> T -> T
  val delete : JClause.T -> T -> T
  val delete_clauses : JClause.T list -> T -> T
  val fold: (JClause.T -> 'a -> 'a) -> T -> 'a -> 'a
  val make : JClause.T list -> T
  val lookup : T -> int -> JClause.T option
  val exists : (JClause.T -> bool) -> T -> bool
  val dest : T -> JClause.T list (* FIXME: performance: eventually remove this *)
  val pretty : Proof.context -> T -> string
end

structure Jeha_Clause_Set : JEHA_CLAUSE_SET =
struct

type T = JClause.T Inttab.table

val empty = Inttab.empty

fun add_new_clause clause = Inttab.update_new (JClause.id clause, clause)

fun add_new_clauses clauses = fold add_new_clause clauses

val delete = Inttab.delete_safe o JClause.id

val delete_clauses = fold delete

fun fold f = Inttab.fold (f o #2)

fun make clauses = add_new_clauses clauses empty

val lookup = Inttab.lookup

fun exists p = Inttab.exists (p o #2)

val dest = map #2 o Inttab.dest

fun pretty ctxt active_set =
  "active: " ^ JClause.pretty_clauses ctxt (dest active_set)

end