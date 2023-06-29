(* o\<lambda>Sup proof logging *)

signature JEHA_LOG =
sig
  datatype inference =
  (* part of the input problem *)
    Axiom of { thm: thm }
  | NegatedConjecture
  (* proper inferences *)
  | Sup of { left_premise: int, right_premise: int, literal: JLit.lpos * JClause_Pos.cpos, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidSup
  | ERes of { premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | EFact of { premise: int, left_literal: JLit.lpos * JClause_Pos.cpos, right_literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | ArgCong
  (* Booleans *)
  | BoolHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FalseElim of { premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | EqHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | NeqHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | ForallHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | ExistsHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | BoolRw of { premise: int, subterm: JClause_Pos.full_pos, subrule: term * term, substitution: Envir.env }
  | ForallRw of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | ExistsRw of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidBoolHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidLoobHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  (* axioms *)
  | Ext
  | Choice
  (* simplification *)
  | DeleteDuplicatedLits of { premise: int, left_literal: JClause_Pos.cpos, right_literal: JClause_Pos.cpos, substitution: Envir.env }
  | DeleteResolvedLits of { premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | RewritePositiveLits of { unit: int, right_premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | RewriteNegativeLits of { unit: int, right_premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | PositiveSimplifyReflect of { unit: int, right_premise: int, disagreement: JClause_Pos.full_pos, substitution: Envir.env }
  | NegativeSimplifyReflect of { unit: int, right_premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | PosOuterClaus of { premise: int, top_level_term: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | NegOuterClaus of { premise: int, top_level_term: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  (* redundancy FIXME: different type? these don't make sense in logs in clauses *)
  | SyntacticTautologyDeletion1 of { premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | SyntacticTautologyDeletion2 of { premise: int, left_literal: JClause_Pos.cpos, right_literal: JClause_Pos.cpos, substitution: Envir.env }
  | ClauseSubsumption of { subsumer: int, subsumed: int, substitution: Envir.env }
  | EqualitySubsumption of { unit: int, disagreement: JClause_Pos.full_pos, substitution: Envir.env }
  (* essentially a NONE value for temporary use *)
  | Invalid
end;

structure Jeha_Log : JEHA_LOG =
struct

datatype inference =
  (* part of the input problem *)
    Axiom of { thm: thm }
  (* do we get a proof of this? (from ccontr?) *)
  | NegatedConjecture
  (* proper inferences *)
  (** general **)
  | Sup of { left_premise: int, right_premise: int, literal: JLit.lpos * JClause_Pos.cpos, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidSup
  | ERes of { premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | EFact of { premise: int, left_literal: JLit.lpos * JClause_Pos.cpos, right_literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | ArgCong
  (** Booleans **)
  | BoolHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FalseElim of { premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | EqHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | NeqHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | ForallHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | ExistsHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | BoolRw of { premise: int, subterm: JClause_Pos.full_pos, subrule: term * term, substitution: Envir.env }
  | ForallRw of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | ExistsRw of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidBoolHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidLoobHoist of { premise: int, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  (** axioms **)
  | Ext
  | Choice
  (** simplification **)
  | DeleteDuplicatedLits of { premise: int, left_literal: JClause_Pos.cpos, right_literal: JClause_Pos.cpos, substitution: Envir.env }
  | DeleteResolvedLits of { premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | RewritePositiveLits of { unit: int, right_premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | RewriteNegativeLits of { unit: int, right_premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | PositiveSimplifyReflect of { unit: int, right_premise: int, disagreement: JClause_Pos.full_pos, substitution: Envir.env }
  | NegativeSimplifyReflect of { unit: int, right_premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | PosOuterClaus of { premise: int, top_level_term: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | NegOuterClaus of { premise: int, top_level_term: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  (* redundancy FIXME: different type? these don't make sense in logs in clauses *)
  | SyntacticTautologyDeletion1 of { premise: int, literal: JClause_Pos.cpos, substitution: Envir.env }
  | SyntacticTautologyDeletion2 of { premise: int, left_literal: JClause_Pos.cpos, right_literal: JClause_Pos.cpos, substitution: Envir.env }
  | ClauseSubsumption of { subsumer: int, subsumed: int, substitution: Envir.env }
  | EqualitySubsumption of { unit: int, disagreement: JClause_Pos.full_pos, substitution: Envir.env }
  (* essentially a NONE value for temporary use *)
  | Invalid

(* Building blocks of proofs (inspired by metis_reconstruct.ML):

substitution / instantiation
  * e.g. as part of Sup: apply unifier \<sigma> to D and to C<u>, then buil the conclusion
  * renaming to make variables disjoint (or is there a better isabelle primitive for this)

superposition with trivial (identity) unification
  * covers Sup, FluidSup, *Hoist (with LEM), BoolRw (with RW rules as left premises), 


BoolHoist: superposition with LEM (x = \<top> \<or> x = \<bottom>)
EqHoist: superposition with LEM 


Justifying simplifications

Deletion of duplicated literals (DD): ??
Deletion of resolved literals (DR): ??
Rewriting of positive/negative literals (RP/RN): instantiation of unit, superposition
Positive simplify-reflect (PS): instantiation of unit, superposition twice, deletion of resolved literal (DR)
Negative simplify-reflect (NS): instantiation of unit, resolution

redundancies (TD1, TD2, SD, CS, ES) don't need to be justified because they delete clauses

How to justify superposition?

D'\<sigma> \<or> u\<sigma> = t'\<sigma>      \<and>       C\<sigma><u\<sigma>>
-----------------------------------
         (D' \<or> C<t'>)\<sigma>

D'\<sigma> \<or> u\<sigma> = t'\<sigma>

resolve with congruence:
u\<sigma> \<noteq> t'\<sigma> \<or> C\<sigma><u\<sigma>> = C\<sigma><t'\<sigma>>




*)

end;
