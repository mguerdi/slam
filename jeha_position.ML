

(*
clause  -> cpos               -> literal
clause  -> lpos * cpos        -> term
clause  -> tpos * lpos * cpos -> term

literal -> lpos               -> term
literal -> tpos * lpos        -> term

term    -> tpos               -> term

Clause.lit_at
Clause.side_at
Clause.term_at

Literal.side_at
Literal.term_at

Term.term_at

(* This encodes - from right to left - positions of literals, sides of equations, positions of
subterms *)
type cpos = ((int list * int) option * bool) option * int

val index_clause : clause -> cpos -> term literal either
fun index_clause c (NONE, i) = Right (nth c i)
  | index_clause c (SOME (NONE, false), i) = Left (#1 (nth c i))
  | index_clause c (SOME (NONE, true), i) = Left (#2 (nth c i))
  | index_clause c (SOME (SOME (js, j), b), i) =
      map_left (subterm_at_tpos (j :: js)) (index_clause c (SOME (NONE, b), i))
*)