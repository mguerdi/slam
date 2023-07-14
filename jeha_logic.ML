(* logial core operations, i.e. term manipulations etc. *)
signature JEHA_LOGIC
sig
  type term
  type literal
  type clause
  type sup_inference = { left: clause, right: clause, unifier: Envir.env option }

  val sup_inference_unifier : sup_inference -> Envir.env

  val superposition : clause -> clause -> clause
end

structure Prover_Logic : JEHA_LOGIC =
struct
  type term = term
  type literal = JLit.T
  type clause = JClause.T
  type sup_inference = { left, right, ... }

  type proof_log = Jeha_Log.inference

  fun sup_inference_unifier { ... } = (* call Jeha_Unify... *)

  fun superposition c d = error ""
end

structure Reconstruction_Logic : JEHA_LOGIC =
struct
  type term = cterm
  type literal = cterm
  (* \<not> A \<Longrightarrow> \<not> B \<Longrightarrow> ... \<Longrightarrow> False *)
  type clause = thm
  type sup_inference = { left, right, ..., unifier }

  (* use the data from the proof log *)
  fun sup_inference_unifier data = #unifier data

  fun superposition c d = error ""
end

(* control flow *)
signature JEHA_PROVER =
sig
  type prover
  val superposition : (sup_data -> bool) -> clause -> clause -> clause
end

signature CONTROLLER =
sig
  type clause_db
  (* the prover state / the proof log *)
  type state
end

functor Prover(Logic: JEHA_LOGIC, Controller: CONTROLLER): JEHA_PROVER =
struct
  type prover = prover_state
  fun superposition checker c d = error "use the underlying logic's operations here"
end

(* In the Saturator, the given clause loop and indices control the rules *)
structure Jeha_Saturator = Prover(Prover_Logic)

(* In the Reconstructor, the proof log controls the rules *)
structure Jeha_Reconstructor = Prover(Reconstruction_Logic)


(* superposition like rules
* Sup
* FluidSup
* *Hoist (with LEM)
* BoolRw (with RW rules as left premises)
*)

(* What sort of checks do we do for superposition like rules?

D' \<or> t = t'      C<u>
----------------------
    (D' \<or> C<t'>)\<sigma>

Before anything:
  (Fluid)Sup 1. u is (not) fluid
  (Fluid)Sup 2. u is (not) a var deeply occuring in C
  Sup 3. variable condition
  BoolHoist 2. u is not variable headed, u is not a fully applied logical symbol
  Eq-/Neq-/Forall-/ExistsHoist, BoolRw 4. if u is variable headed, it must be applied ... 
  BoolHoist 3. u is >-eligible in C (* this is probably the same as elibibility w.r.t. \<sigma> *)
  BoolHoist 4. the occurence of u is not at the top level of a positive literal
  BoolRw 2. u is not a variable
After unification, before conclusion:
  (Fluid)Sup 5. \<not> (t\<sigma> < t'\<sigma>)
  Sup, Eq-/Neq-/Forall-/ExistsHoist, BoolRw 6. u is >-eligible in C w.r.t \<sigma>
  Sup 7. \<not> (C\<sigma> < D\<sigma>)
  Sup 8. t = t' is strictly >-eligible in D w.r.t. \<sigma>
  Sup 9. t\<sigma> is not a fully applied logical symbol
  (Fluid)Sup 10. if t'\<sigma> = \<bottom> then position of u is at top level of pos. literal
  FluidSup 4. (z t')\<sigma> \<noteq> (z t)\<sigma>
After building conclusion:

*)
