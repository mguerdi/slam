(* o\<lambda>Sup proof logging *)

signature JEHA_LOG =
sig
  datatype 'a inference =
  (* part of the input problem or auxilliary like lem, boolean tautologies *)
    Axiom of { thm: thm }
  (* proper inferences *)
  | Sup of { left_premise: 'a, left_premise_shift: int, right_premise: 'a, literal: JLit.lpos * JClause_Pos.cpos, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidSup
  | ERes of { premise: 'a, literal: JClause_Pos.cpos, substitution: Envir.env }
  | EFact of { premise: 'a, left_literal: JLit.lpos * JClause_Pos.cpos, right_literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | ArgCong of { premise: 'a, literal: JClause_Pos.cpos, number_of_vars: int }
  (* Booleans *)
  | BoolHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FalseElim of { premise: 'a, literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | EqHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | NeqHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | ForallHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env, fresh_x: term }
  | ExistsHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env, fresh_x: term }
  | BoolRw of { premise: 'a, subterm: JClause_Pos.full_pos, subrule: term * term, substitution: Envir.env }
  | ForallRw of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | ExistsRw of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidBoolHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidLoobHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  (* axioms *)
  | Ext
  | Choice
  (* simplification *)
  (* FIXME: | DeleteDuplicatedLits of { premise: 'a, left_literal: JClause_Pos.cpos, right_literal: JClause_Pos.cpos, substitution: Envir.env } *)
  | DeleteDuplicatedLits of { premise: 'a, duplicate_cposs: { duplicate: JClause_Pos.cpos, duplicate_of: JClause_Pos.cpos } list }
  (* FIXME: | DeleteResolvedLits of { premise: 'a, literal: JClause_Pos.cpos, substitution: Envir.env } *)
  | DeleteResolvedLits of { premise: 'a, cposs: JClause_Pos.cpos list }
  | RewritePositiveLits of { unit: 'a, unit_shift: int, unit_orientation: JLit.lpos, right_premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | RewriteNegativeLits of { unit: 'a, unit_shift: int, unit_orientation: JLit.lpos, right_premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  (* FIXME: add substitution *)
  | PositiveSimplifyReflect of { unit: 'a, unit_shift: int, matcher: Envir.env, unit_orientation: JLit.lpos, right_premise: 'a, disagreement: JClause_Pos.full_pos }
  (* FIXME: add substitution *)
  | NegativeSimplifyReflect of { unit: 'a, substitution: Envir.env, unit_shift : int, right_premise: 'a, literal: JClause_Pos.cpos }
  (* | PosOuterClaus of { premise: 'a, top_level_term: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | NegOuterClaus of { premise: 'a, top_level_term: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env } *)
  | SimpPosNegOuterClaus of { premise: 'a, literal: JClause_Pos.cpos, conclusion_index: int }
  (* *)
  | SimpBoolRw of { premise: 'a, subterm: JClause_Pos.full_pos, subrule: term * term, substitution: Envir.env }
  | SimpFalseElim of { premise: 'a, literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | SimpNormalizePredLits of { premise: 'a }
  (* redundancy FIXME: different type? these don't make sense in logs in clauses *)
  | SyntacticTautologyDeletion1 of { premise: 'a, literal: JClause_Pos.cpos, substitution: Envir.env }
  | SyntacticTautologyDeletion2 of { premise: 'a, left_literal: JClause_Pos.cpos, right_literal: JClause_Pos.cpos, substitution: Envir.env }
  | ClauseSubsumption of { subsumer: int, subsumed: int, substitution: Envir.env }
  | EqualitySubsumption of { unit: 'a, disagreement: JClause_Pos.full_pos, substitution: Envir.env }
  (* essentially a NONE value for temporary use *)
  | Invalid

  val premises : 'a inference -> 'a list
  val premises_shift_substitution : int inference -> { id: int, shift: int, substitution: Envir.env } list
  val name_of : 'a inference -> string
  val pretty : Proof.context -> 'a inference -> string
end;

structure Jeha_Log : JEHA_LOG =
struct

datatype 'a inference =
  (* part of the input problem or auxilliary like lem, boolean tautologies *)
    Axiom of { thm: thm }
  (* proper inferences *)
  (** general **)
  | Sup of { left_premise: 'a, left_premise_shift: int, right_premise: 'a, literal: JLit.lpos * JClause_Pos.cpos, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidSup
  | ERes of { premise: 'a, literal: JClause_Pos.cpos, substitution: Envir.env }
  | EFact of { premise: 'a, left_literal: JLit.lpos * JClause_Pos.cpos, right_literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | ArgCong of { premise: 'a, literal: JClause_Pos.cpos, number_of_vars: int }
  (** Booleans **)
  | BoolHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FalseElim of { premise: 'a, literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | EqHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | NeqHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | ForallHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env, fresh_x: term }
  | ExistsHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env, fresh_x: term }
  | BoolRw of { premise: 'a, subterm: JClause_Pos.full_pos, subrule: term * term, substitution: Envir.env }
  | ForallRw of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | ExistsRw of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidBoolHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidLoobHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  (** axioms **)
  | Ext
  | Choice
  (** simplification **)
  | DeleteDuplicatedLits of { premise: 'a, duplicate_cposs: { duplicate: JClause_Pos.cpos, duplicate_of: JClause_Pos.cpos } list }
  | DeleteResolvedLits of { premise: 'a, cposs: JClause_Pos.cpos list }
  | RewritePositiveLits of { unit: 'a, unit_shift: int, unit_orientation: JLit.lpos, right_premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | RewriteNegativeLits of { unit: 'a, unit_shift: int, unit_orientation: JLit.lpos, right_premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | PositiveSimplifyReflect of { unit: 'a, unit_shift: int, matcher: Envir.env, unit_orientation: JLit.lpos, right_premise: 'a, disagreement: JClause_Pos.full_pos }
  | NegativeSimplifyReflect of { unit: 'a, substitution: Envir.env, unit_shift : int, right_premise: 'a, literal: JClause_Pos.cpos }
  | SimpPosNegOuterClaus of { premise: 'a, literal: JClause_Pos.cpos, conclusion_index: int }
  | SimpBoolRw of { premise: 'a, subterm: JClause_Pos.full_pos, subrule: term * term, substitution: Envir.env }
  | SimpFalseElim of { premise: 'a, literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | SimpNormalizePredLits of { premise: 'a }
  (* redundancy FIXME: different type? these don't make sense in logs in clauses *)
  | SyntacticTautologyDeletion1 of { premise: 'a, literal: JClause_Pos.cpos, substitution: Envir.env }
  | SyntacticTautologyDeletion2 of { premise: 'a, left_literal: JClause_Pos.cpos, right_literal: JClause_Pos.cpos, substitution: Envir.env }
  | ClauseSubsumption of { subsumer: int, subsumed: int, substitution: Envir.env }
  | EqualitySubsumption of { unit: 'a, disagreement: JClause_Pos.full_pos, substitution: Envir.env }
  (* essentially a NONE value for temporary use *)
  | Invalid

fun premises (Axiom { thm: thm }) = []
  | premises (Sup { left_premise, right_premise, ... }) = [left_premise, right_premise]
  | premises FluidSup = error "FluidSup undefined"
  | premises (ERes { premise, ... }) = [premise]
  | premises (EFact { premise, ... }) = [premise]
  | premises (ArgCong { premise, ... }) = [premise]
  | premises (BoolHoist { premise, ... }) = [premise]
  | premises (FalseElim { premise, ... }) = [premise]
  | premises (EqHoist { premise, ... }) = [premise]
  | premises (NeqHoist { premise, ... }) = [premise]
  | premises (ForallHoist { premise, ... }) = [premise]
  | premises (ExistsHoist { premise, ... }) = [premise]
  | premises (BoolRw { premise, ... }) = [premise]
  | premises (ForallRw { premise, ... }) = [premise]
  | premises (ExistsRw { premise, ... }) = [premise]
  | premises (FluidBoolHoist { premise, ... }) = [premise]
  | premises (FluidLoobHoist { premise, ... }) = [premise]
  | premises Ext = error "Ext undefined"
  | premises Choice = error "Choice undefined"
  | premises (DeleteDuplicatedLits { premise, ... }) = [premise]
  | premises (DeleteResolvedLits { premise, ... }) = [premise]
  | premises (RewritePositiveLits { unit, right_premise, ... }) = [unit, right_premise]
  | premises (RewriteNegativeLits { unit, right_premise, ... }) = [unit, right_premise]
  | premises (PositiveSimplifyReflect { unit, right_premise, ... }) = [unit, right_premise]
  | premises (NegativeSimplifyReflect { unit, right_premise, ... }) = [unit, right_premise]
  | premises (SimpPosNegOuterClaus { premise, ... }) = [premise]
  | premises (SimpBoolRw { premise, ...}) = [premise]
  | premises (SimpFalseElim { premise, ... }) = [premise]
  | premises (SimpNormalizePredLits { premise }) = [premise]
  | premises Invalid = error "\"Invalid\" inference encountered"

fun premises_shift_substitution (Sup { left_premise, left_premise_shift, right_premise, substitution, ... })
      = [{ id = left_premise, shift = left_premise_shift, substitution = substitution }, { id = right_premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (RewritePositiveLits { unit, unit_shift, right_premise, substitution, ... })
      = [{ id = unit, shift = unit_shift, substitution = substitution }, { id = right_premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (RewriteNegativeLits log) 
      = premises_shift_substitution (RewritePositiveLits log) 
  | premises_shift_substitution (ERes { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (EFact { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  (* | premises_shift_substitution (ArgCong { premise, number_of_vars, ... })
      = [{ id = premise, shift = 0, substitution = substitution }] *)
  | premises_shift_substitution (BoolHoist { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (FalseElim { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (EqHoist { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (NeqHoist { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (ForallHoist { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (ExistsHoist { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (BoolRw { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (ForallRw { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (ExistsRw { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (FluidBoolHoist { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (FluidLoobHoist { premise, substitution, ... })
      = [{ id = premise, shift = 0, substitution = substitution }]
  | premises_shift_substitution (NegativeSimplifyReflect { unit, substitution, unit_shift, right_premise, ... })
      = [{ id = unit, shift = unit_shift, substitution = substitution }, { id = right_premise, shift = 0, substitution = Envir.init }]
  | premises_shift_substitution other =
      let
        val premises = premises other
      in
        premises |> map (fn id => { id = id, shift = 0, substitution = Envir.init })
      end

(* Building blocks of proofs (inspired by metis_reconstruct.ML):

substitution / instantiation
  * e.g. as part of Sup: apply unifier \<sigma> to D and to C<u>, then build the conclusion
  * renaming to make variables disjoint (or is there a better isabelle primitive for this)

normalization
  * Q\<^sub>\<approx>-normal form (preprocessing)
  * \<beta>\<eta>Q\<^sub>\<eta>-normal form

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
u\<sigma> = t'\<sigma> \<Longrightarrow> C\<sigma><u\<sigma>> = C\<sigma><t'\<sigma>>



How to justify fluid superposition?

Assume \<sigma> \<in> CSU(z t, u) has already been applied

D' \<or> t = t'      \<and>       C<z\<sigma> t>
-------------------------------- FluidSup
         (D' \<or> C<z\<sigma> t'>)

argument congruence:
t = t' => z\<sigma> t = z\<sigma> t'

C-congurence
z\<sigma> t = z\<sigma> t' => C<z\<sigma> t> = C<z\<sigma> t'>


*)


fun name_of (Axiom _) = "Axiom"
  | name_of (Sup _) = "Sup" 
  | name_of FluidSup = "FluidSup"
  | name_of (ERes _) = "ERes" 
  | name_of (EFact _) = "EFact" 
  | name_of (ArgCong _) = "ArgCong" 
  | name_of (BoolHoist _) = "BoolHoist" 
  | name_of (FalseElim _) = "FalseElim" 
  | name_of (EqHoist _) = "EqHoist" 
  | name_of (NeqHoist _) = "NeqHoist" 
  | name_of (ForallHoist _) = "\<forall>Hoist" 
  | name_of (ExistsHoist _) = "\<exists>Hoist" 
  | name_of (BoolRw _) = "BoolRw" 
  | name_of (ForallRw _) = "\<forall>Rw" 
  | name_of (ExistsRw _) = "\<exists>Rw" 
  | name_of (FluidBoolHoist _) = "FluidBoolHoist" 
  | name_of (FluidLoobHoist _) = "FluidLoobHoist" 
  | name_of Ext = "Ext" 
  | name_of Choice = "Choice" 
  | name_of (DeleteDuplicatedLits _) = "DeleteDuplicatedLits" 
  | name_of (DeleteResolvedLits _) = "DeleteResolvedLits" 
  | name_of (RewritePositiveLits _) = "RewritePositiveLits" 
  | name_of (RewriteNegativeLits _) = "RewriteNegativeLits" 
  | name_of (PositiveSimplifyReflect _) = "PositiveSimplifyReflect" 
  | name_of (NegativeSimplifyReflect _) = "NegativeSimplifyReflect" 
  | name_of (SimpPosNegOuterClaus _) = "SimpPosNegOuterClaus"
  | name_of (SyntacticTautologyDeletion1 _) = "SyntacticTautologyDeletion1" 
  | name_of (SyntacticTautologyDeletion2 _) = "SyntacticTautologyDeletion2" 
  | name_of (ClauseSubsumption _) = "ClauseSubsumption" 
  | name_of (EqualitySubsumption _) = "EqualitySubsumption" 
  | name_of (SimpBoolRw _) = "SimpBoolRw"
  | name_of (SimpFalseElim _) = "SimpFalseElim" 
  | name_of (SimpNormalizePredLits _) = "SimpNormalizePredLits"
  | name_of Invalid = "Invalid" 

fun pretty ctxt inference = case inference of
    Axiom { thm = thm } => "Axiom:" ^ Thm.string_of_thm ctxt thm (* shows hyps *)
  | _ => @{make_string} inference

end;
