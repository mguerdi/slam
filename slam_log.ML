(* o\<lambda>Sup proof logging *)

signature SLAM_LOG =
sig
  datatype 'a inference =
  (* part of the input problem or auxilliary like lem, boolean tautologies *)
    Axiom of { thm: thm }
  | NegatedConjecture of { thm: thm }
  (* proper inferences *)
  | Sup of { left_premise: 'a, left_premise_shift: int, right_premise: 'a, literal: JLit.lpos * JClause_Pos.cpos, subterm: JClause_Pos.full_pos, preunifier: Slam_Unify.preunifier }
  | FluidSup
  | ERes of { premise: 'a, literal: JClause_Pos.cpos, substitution: Envir.env }
  | EFact of { premise: 'a, left_literal: JLit.lpos * JClause_Pos.cpos, right_literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | ArgCong of { premise: 'a, substitution: Envir.env, literal: JClause_Pos.cpos, vars: term list }
  (* Booleans *)
  | BoolHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FalseElim of { premise: 'a, literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | EqHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | NeqHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | ForallHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env, fresh_x: term }
  | ExistsHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env, fresh_x: term }
  | BoolRw of { premise: 'a, subterm: JClause_Pos.full_pos, subrule: term * term, substitution: Envir.env }
  | ForallRw of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env, skolems: (term * term * term) list }
  | ExistsRw of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env, skolems: (term * term * term) list }
  | FluidBoolHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidLoobHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  (* axioms *)
  | Ext
  | NegExt of { premise: 'a, literal: JClause_Pos.cpos, skolems: (term * term * term) list }
  | NegCongFun of { premise: 'a, literal: JClause_Pos.cpos, number_of_new_lits: int }
  | Choice
  (* simplification *)
  (* FIXME: | DeleteDuplicatedLits of { premise: 'a, left_literal: JClause_Pos.cpos, right_literal: JClause_Pos.cpos, substitution: Envir.env } *)
  | DeleteDuplicatedLits of { premise: 'a, duplicate_cposs: { duplicate: JClause_Pos.cpos, duplicate_of: JClause_Pos.cpos, orientation: JLit.lpos } list }
  (* FIXME: | DeleteResolvedLits of { premise: 'a, literal: JClause_Pos.cpos, substitution: Envir.env } *)
  | DeleteResolvedLits of { premise: 'a, cposs: JClause_Pos.cpos list }
  | FlexFlexSimp of { premise: 'a }
  | RewritePositiveLits of { unit: 'a, unit_shift: int, unit_orientation: JLit.lpos, right_premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | RewriteNegativeLits of { unit: 'a, unit_shift: int, unit_orientation: JLit.lpos, right_premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | PositiveSimplifyReflect of { unit: 'a, unit_shift: int, matcher: Envir.env, unit_orientation: JLit.lpos, right_premise: 'a, disagreement: JClause_Pos.full_pos }
  | NegativeSimplifyReflect of { unit: 'a, unit_shift : int, matcher: Envir.env, unit_orientation: JLit.lpos, right_premise: 'a, literal: JClause_Pos.cpos }
  (* | PosOuterClaus of { premise: 'a, top_level_term: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | NegOuterClaus of { premise: 'a, top_level_term: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env } *)
  | SimpPosNegOuterClaus of { premise: 'a, literal: JClause_Pos.cpos, conclusion_index: int, quant_info: (term * (term, (term * term * term)) Slam_Common.either) option }
  (* *)
  | SimpBoolRw of { premise: 'a, subterm: JClause_Pos.full_pos, subrule: term * term, substitution: Envir.env }
  | SimpFalseElim of { premise: 'a, literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  (* redundancy FIXME: different type? these don't make sense in logs in clauses *)
  | SyntacticTautologyDeletion1 of { premise: 'a, literal: JClause_Pos.cpos, substitution: Envir.env }
  | SyntacticTautologyDeletion2 of { premise: 'a, left_literal: JClause_Pos.cpos, right_literal: JClause_Pos.cpos, substitution: Envir.env }
  | ClauseSubsumption of { subsumer: int, subsumed: int, substitution: Envir.env }
  | EqualitySubsumption of { unit: 'a, disagreement: JClause_Pos.full_pos, substitution: Envir.env }
  (* essentially a NONE value for temporary use *)
  | Invalid

  val is_simplification : 'a inference -> bool
  val premises : 'a inference -> 'a list
  (* val premises_shift_substitution : int inference -> { id: int, shift: int, substitution: Envir.env } list *)
  val name_of : 'a inference -> string
  val pretty' : Proof.context -> int inference -> Pretty.T
  val pretty : Proof.context -> int inference -> string
end;

structure Slam_Log : SLAM_LOG =
struct

datatype 'a inference =
  (* part of the input problem or auxilliary like lem, boolean tautologies *)
    Axiom of { thm: thm }
  | NegatedConjecture of { thm: thm }
  (* proper inferences *)
  (** general **)
  | Sup of { left_premise: 'a, left_premise_shift: int, right_premise: 'a, literal: JLit.lpos * JClause_Pos.cpos, subterm: JClause_Pos.full_pos, preunifier: Slam_Unify.preunifier }
  | FluidSup
  | ERes of { premise: 'a, literal: JClause_Pos.cpos, substitution: Envir.env }
  | EFact of { premise: 'a, left_literal: JLit.lpos * JClause_Pos.cpos, right_literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | ArgCong of { premise: 'a, substitution: Envir.env, literal: JClause_Pos.cpos, vars: term list }
  (** Booleans **)
  | BoolHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FalseElim of { premise: 'a, literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  | EqHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | NeqHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | ForallHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env, fresh_x: term }
  | ExistsHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env, fresh_x: term }
  | BoolRw of { premise: 'a, subterm: JClause_Pos.full_pos, subrule: term * term, substitution: Envir.env }
  | ForallRw of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env, skolems: (term * term * term) list }
  | ExistsRw of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env, skolems: (term * term * term) list } 
  | FluidBoolHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | FluidLoobHoist of { premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  (** axioms **)
  | Ext
  | NegExt of { premise: 'a, literal: JClause_Pos.cpos, skolems: (term * term * term) list }
  | NegCongFun of { premise: 'a, literal: JClause_Pos.cpos, number_of_new_lits: int }
  | Choice
  (** simplification **)
  | DeleteDuplicatedLits of { premise: 'a, duplicate_cposs: { duplicate: JClause_Pos.cpos, duplicate_of: JClause_Pos.cpos, orientation: JLit.lpos } list }
  | DeleteResolvedLits of { premise: 'a, cposs: JClause_Pos.cpos list }
  | FlexFlexSimp of { premise: 'a }
  | RewritePositiveLits of { unit: 'a, unit_shift: int, unit_orientation: JLit.lpos, right_premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | RewriteNegativeLits of { unit: 'a, unit_shift: int, unit_orientation: JLit.lpos, right_premise: 'a, subterm: JClause_Pos.full_pos, substitution: Envir.env }
  | PositiveSimplifyReflect of { unit: 'a, unit_shift: int, matcher: Envir.env, unit_orientation: JLit.lpos, right_premise: 'a, disagreement: JClause_Pos.full_pos }
  | NegativeSimplifyReflect of { unit: 'a, unit_shift : int, matcher: Envir.env, unit_orientation: JLit.lpos, right_premise: 'a, literal: JClause_Pos.cpos }
  | SimpPosNegOuterClaus of { premise: 'a, literal: JClause_Pos.cpos, conclusion_index: int, quant_info: (term * (term, (term * term * term)) Slam_Common.either) option }
  | SimpBoolRw of { premise: 'a, subterm: JClause_Pos.full_pos, subrule: term * term, substitution: Envir.env }
  | SimpFalseElim of { premise: 'a, literal: JLit.lpos * JClause_Pos.cpos, substitution: Envir.env }
  (* redundancy FIXME: different type? these don't make sense in logs in clauses *)
  | SyntacticTautologyDeletion1 of { premise: 'a, literal: JClause_Pos.cpos, substitution: Envir.env }
  | SyntacticTautologyDeletion2 of { premise: 'a, left_literal: JClause_Pos.cpos, right_literal: JClause_Pos.cpos, substitution: Envir.env }
  | ClauseSubsumption of { subsumer: int, subsumed: int, substitution: Envir.env }
  | EqualitySubsumption of { unit: 'a, disagreement: JClause_Pos.full_pos, substitution: Envir.env }
  (* essentially a NONE value for temporary use *)
  | Invalid

fun is_simplification (Axiom _) = false
  | is_simplification (NegatedConjecture _) = false
  | is_simplification (Sup _) = false
  | is_simplification FluidSup = false
  | is_simplification (ERes _) = false
  | is_simplification (EFact _) = false
  | is_simplification (ArgCong _) = false
  | is_simplification (BoolHoist _) = false
  | is_simplification (FalseElim _) = false
  | is_simplification (EqHoist _) = false
  | is_simplification (NeqHoist _) = false
  | is_simplification (ForallHoist _) = false
  | is_simplification (ExistsHoist _) = false
  | is_simplification (BoolRw _) = false
  | is_simplification (ForallRw _) = false
  | is_simplification (ExistsRw _) = false
  | is_simplification (FluidBoolHoist _) = false
  | is_simplification (FluidLoobHoist _) = false
  | is_simplification Ext = false
  | is_simplification (NegExt _) = false
  | is_simplification (NegCongFun _) = false
  | is_simplification Choice = false
  | is_simplification (DeleteDuplicatedLits _) = true
  | is_simplification (DeleteResolvedLits _) = true
  | is_simplification (FlexFlexSimp _) = true
  | is_simplification (RewritePositiveLits _) = true
  | is_simplification (RewriteNegativeLits _) = true
  | is_simplification (PositiveSimplifyReflect _) = true
  | is_simplification (NegativeSimplifyReflect _) = true
  | is_simplification (SimpPosNegOuterClaus _) = true
  | is_simplification (SimpBoolRw _) = true
  | is_simplification (SimpFalseElim _) = true
  | is_simplification Invalid = false
  | is_simplification _ = false

fun premises (Axiom _) = []
  | premises (NegatedConjecture _) = []
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
  | premises (NegExt { premise, ...}) = [premise]
  | premises (NegCongFun { premise, ... }) = [premise]
  | premises Choice = error "Choice undefined"
  | premises (DeleteDuplicatedLits { premise, ... }) = [premise]
  | premises (DeleteResolvedLits { premise, ... }) = [premise]
  | premises (FlexFlexSimp { premise }) = [premise]
  | premises (RewritePositiveLits { unit, right_premise, ... }) = [unit, right_premise]
  | premises (RewriteNegativeLits { unit, right_premise, ... }) = [unit, right_premise]
  | premises (PositiveSimplifyReflect { unit, right_premise, ... }) = [unit, right_premise]
  | premises (NegativeSimplifyReflect { unit, right_premise, ... }) = [unit, right_premise]
  | premises (SimpPosNegOuterClaus { premise, ... }) = [premise]
  | premises (SimpBoolRw { premise, ...}) = [premise]
  | premises (SimpFalseElim { premise, ... }) = [premise]
  | premises Invalid = error "\"Invalid\" inference encountered"
  | premises _ = error "Slam_Log.premises: unimplemented"

(* FIXME: delete? *)
(*
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
  | premises_shift_substitution (NegativeSimplifyReflect { unit, matcher, unit_shift, right_premise, ... })
      = [{ id = unit, shift = unit_shift, substitution = matcher }, { id = right_premise, shift = 0, substitution = Envir.init }]
  | premises_shift_substitution other =
      let
        val premises = premises other
      in
        premises |> map (fn id => { id = id, shift = 0, substitution = Envir.init })
      end
*)

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
  | name_of (NegatedConjecture _) = "NegatedConjecture"
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
  | name_of (NegExt _) = "NegExt"
  | name_of (NegCongFun _) = "NegCongFun"
  | name_of Choice = "Choice" 
  | name_of (DeleteDuplicatedLits _) = "DeleteDuplicatedLits" 
  | name_of (DeleteResolvedLits _) = "DeleteResolvedLits" 
  | name_of (FlexFlexSimp _) = "FlexFlexSimp"
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
  | name_of Invalid = "Invalid" 
  | name_of _ = error "Slam_Log.name_of: unimplemented"

open Pretty

fun pretty' ctxt (inference: int inference) =
  let
    val lbl = Slam_Common.label_pretty
    val lst = Pretty.enum ";" "{" "}"
    val penv = Slam_Common.pretty_env' ctxt
    val ppreunif  = Slam_Common.pretty_preunifier' ctxt
    val pretty_skolems' = list "[" "]" o map (fn (t1, t2, t3) => Slam_Common.pretty_terms' ctxt [t1, t2, t3])
    fun pretty_subrule' subrule = Pretty.block [Slam_Common.pretty_term' ctxt (#1 subrule), str " \<mapsto> ", Slam_Common.pretty_term' ctxt (#2 subrule)]
  in
  case inference of
    Axiom { thm } => lst [str "Axiom", Thm.pretty_thm ctxt thm]
  | NegatedConjecture { thm } => lst [str "NegatedConjecture", Thm.pretty_thm ctxt thm]
  | Sup { left_premise, left_premise_shift, right_premise, literal, subterm, preunifier }
     => lst [str "Sup", lbl "left" (@{mk_pty} left_premise), lbl "shift" (@{mk_pty} left_premise_shift), @{mk_pty} literal, lbl "right" (@{mk_pty} right_premise), @{mk_pty} subterm, ppreunif preunifier]
  | FluidSup => str "FluidSup"
  | ERes { premise, literal, substitution} => lst [str "ERes", @{mk_pty} premise, @{mk_pty} literal, penv substitution]
  | EFact { premise, left_literal, right_literal, substitution } => lst [str "EFact", @{mk_pty} premise, @{mk_pty} left_literal, @{mk_pty} right_literal, penv substitution]
  | ArgCong { premise, substitution, literal, vars } => lst [str "ArgCong", @{mk_pty} premise, penv substitution, @{mk_pty} literal, Slam_Common.pretty_terms' ctxt vars]
  | BoolHoist { premise, subterm, substitution } => lst [str "BoolHoist", @{mk_pty} premise, @{mk_pty} subterm, penv substitution]
  | FalseElim { premise, literal, substitution } => lst [str "FalseElim", @{mk_pty} premise, @{mk_pty} literal, penv substitution]
  | EqHoist { premise, subterm, substitution } => lst [str "EqHoist", @{mk_pty} premise, @{mk_pty} subterm, penv substitution]
  | NeqHoist { premise, subterm, substitution } => lst [str "NeqHoist", @{mk_pty} premise, @{mk_pty} subterm, penv substitution]
  | ForallHoist { premise, subterm, substitution, fresh_x } => lst [str "ForallHoist", @{mk_pty} premise, @{mk_pty} subterm, penv substitution, Slam_Common.pretty_term' ctxt fresh_x]
  | ExistsHoist { premise, subterm, substitution, fresh_x } => lst [str "ExistsHoist", @{mk_pty} premise, @{mk_pty} subterm, penv substitution, Slam_Common.pretty_term' ctxt fresh_x]
  | BoolRw { premise, subterm, subrule, substitution } => lst [str "BoolRw", @{mk_pty} premise, @{mk_pty} subterm, pretty_subrule' subrule, penv substitution]
  | ForallRw { premise, subterm, substitution, skolems } => lst [str "ForallRw", @{mk_pty} premise, @{mk_pty} subterm, penv substitution, pretty_skolems' skolems]
  | ExistsRw { premise, subterm, substitution, skolems } => lst [str "ExistsRw", @{mk_pty} premise, @{mk_pty} subterm, penv substitution, pretty_skolems' skolems]
  | FluidBoolHoist _ => lst [str "FluidBoolHoist"]
  | FluidLoobHoist _ => lst [str "FluidLoobHoist"]
  | Ext => lst [str "Ext"]
  | NegExt { premise, literal, skolems } => lst [str "NegExt", @{mk_pty} premise, @{mk_pty} literal, pretty_skolems' skolems]
  | NegCongFun { premise, literal, number_of_new_lits } => lst [str "NegCongFun", @{mk_pty} premise, @{mk_pty} literal, @{mk_pty} number_of_new_lits]
  | Choice => lst [str "Choice"]
  | DeleteDuplicatedLits { premise, duplicate_cposs }
      => lst [str "DeleteDuplicatedLits", @{mk_pty} premise, @{mk_pty} duplicate_cposs]
  | DeleteResolvedLits { premise, cposs }
      => lst [str "DeleteResolvedLits", @{mk_pty} premise, @{mk_pty} cposs]
  | FlexFlexSimp { premise } => lst [str "FlexFlexSimp", @{mk_pty} premise]
  | RewritePositiveLits { unit, unit_shift, unit_orientation, right_premise, subterm, substitution }
       => lst [str "RewritePositiveLits", @{mk_pty} unit, lbl "shift" (@{mk_pty} unit_shift), @{mk_pty} unit_orientation, @{mk_pty} right_premise, @{mk_pty} subterm, penv substitution]
  | RewriteNegativeLits { unit, unit_shift, unit_orientation, right_premise, subterm, substitution }
       => lst [str "RewriteNegativeLits", @{mk_pty} unit, lbl "shift" (@{mk_pty} unit_shift), @{mk_pty} unit_orientation, @{mk_pty} right_premise, @{mk_pty} subterm, penv substitution]
  | PositiveSimplifyReflect { unit, unit_shift, matcher, unit_orientation, right_premise, disagreement }
       => lst [str "PositiveSimplifyReflect", @{mk_pty} unit, lbl "shift" (@{mk_pty} unit_shift), penv matcher, @{mk_pty} unit_orientation, @{mk_pty} right_premise, @{mk_pty} disagreement]
  | NegativeSimplifyReflect { unit, unit_shift , matcher, unit_orientation, right_premise, literal }
       => lst [str "NegativeSimplifyReflect", @{mk_pty} unit, lbl "shift" (@{mk_pty} unit_shift), penv matcher, @{mk_pty} unit_orientation, @{mk_pty} right_premise, @{mk_pty} literal]
  | SimpPosNegOuterClaus { premise, literal, conclusion_index, quant_info }
       => lst [str "SimpPosNegOuterClaus", @{mk_pty} premise, @{mk_pty} literal, @{mk_pty} conclusion_index, @{mk_pty} quant_info]
  | SimpBoolRw { premise, subterm, subrule, substitution }
       => lst [str "SimpBoolRw", @{mk_pty} premise, @{mk_pty} subterm, pretty_subrule' subrule, penv substitution]
  | SimpFalseElim { premise, literal, substitution }
       => lst [str "SimpFalseElim", @{mk_pty} premise, @{mk_pty} literal, penv substitution]
  (*
  | SyntacticTautologyDeletion1 { premise, literal, substitution }
       => lst [str "SyntacticTautologyDeletion1"]
  | SyntacticTautologyDeletion2 { premise, left_literal, right_literal, substitution }
       => lst [str "SyntacticTautologyDeletion2"]
  | ClauseSubsumption { subsumer, subsumed, substitution }
       => lst [str "ClauseSubsumption"]
  | EqualitySubsumption { unit, disagreement, substitution }
       => lst [str "EqualitySubsumption"]
       *)
  (* essentially a NONE value for temporary use *)
  | Invalid
       => str "Invalid"
  end

fun pretty ctxt inference = Pretty.string_of (pretty' ctxt inference)

end;
