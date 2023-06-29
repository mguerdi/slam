(* detailed proof and proof reconstruction *)

signature JEHA_PROOF =
sig
  type proof_step
  val hol_thm_of_clause : (int -> JClause.T) -> int -> thm
  (* elaborates a \<lambda>oSup inference into a series of more smaller proof steps *)
  val fun proof_steps_of_inference : Jeha_Log.inference -> proof_step
end;

structure Jeha_Proof : JEHA_PROOF = 
struct

(* The primitve building blocks to which all o\<lambda>Sup inferences can be reduced. *)
datatype proof_step =
    (* FIXME: does normalization need to be separate? *)
    Instantiation of { premise: int, substitution: Envir.env }
  | Sup of { left_premise: int, right_premise: int, literal: JLit.lpos * JClause_Pos.cpos, subterm: JClause_Pos.full_pos }
  | ERes of { premise: int, literal: JClause_Pos.cpos }
  | EFact of { premise: int, left_literal: JLit.lpos * JClause_Pos.cpos, right_literal: JLit.lpos * JClause_Pos.cpos }
  (* FIXME: can this be meaningfully viewed as a kind of superposition? *)
  | ArgCong 
  | 

fun proof_steps_of_inference 

(* turn jeha clause [A, B, C] into formula \<not>A \<Longrightarrow> \<not>B \<Longrightarrow> \<not>C \<Longrightarrow> False *)
fun hol_of_clause c =
  let
    val negated_literals = 
      JClause.literals c
      |> (fn (s, t, b) => (s, t, not b))
      |> map JLit.term_of
  in
    Logic.list_implies negated_literals @{term "False"}
  end

(* with index 2 turn \<not>A \<Longrightarrow> \<not>B \<Longrightarrow> \<not>C \<Longrightarrow> False into \<not>A \<Longrightarrow> \<not>C \<Longrightarrow> B *)
(* fun move_literal_to_conclusion literal_index *)


fun hol_thm_of_clause (clause_db : int -> JClause.T) clause_id =
  let
    val clause = clause_db clause_id
    val inference = JClause.origin clause
  in
    (* Idea: recurse until initial nodes (axioms, negated conjecture, etc.) have
    been reached. Turn those into theorems and return them. For interior nodes,
    use the theorems corresponding to the premises to reconstruct the conclusion
    in such a way that it's structure matches that of the corresponding clause
    in the database (check this property). *)
    case inference of
      Sup => error "hol_thm_of_clause unimplemented"
    | ERes => error "hol_thm_of_clause unimplemented"
    | _ => error "hol_thm_of_clause unimplemented"

end;