theory paper_example_25

imports JEHA_TEST_BASE.test_base

begin

declare [[jeha_trace]]

(* FIXME: Doesn't work with select_all_neg_lit even with jeha_max_number_of_steps set to 1000.
Increasing to 2000 eventually leads to Interrupt_Breakdown. *)
(* declare [[jeha_literal_selection_function="select_all_neg_lit"]] *)

lemma paper_example_25_all_rules:
  shows "(\<And>z. z a \<Longrightarrow> z b) \<Longrightarrow> a = b"
  (* by metis (* fails *) *)
  using [[(* show_types, ML_print_depth=100, ML_exception_trace, jeha_trace_archive, *) jeha_trace_forward_simp, jeha_trace_simp_steps (* jeha_trace_inferred, jeha_trace_cheap_simp *)]]
  by jeha (* 337 ms *)

declare [[jeha_disable_all]]

declare [[jeha_rule_eq_hoist]]
declare [[jeha_rule_bool_rw]]
declare [[jeha_rule_false_elim]]
declare [[jeha_rule_sup]]
declare [[jeha_rule_e_res]]

(* To reach the initial clause set of example 25. *)
declare [[jeha_rule_forall_hoist]]
(* declare [[jeha_rule_bool_hoist]] *)
declare [[jeha_rule_simp_outer_claus]]

(* necessary *)
declare [[jeha_rule_clause_subsumption]]

declare [[jeha_rule_simp_bool_rw]]
declare [[jeha_rule_simp_false_elim]]

(*
ML \<open>
  val leibniz = Skip_Proof.make_thm @{theory} (HOLogic.mk_Trueprop @{term_schem "?z (a :: 'a) = False \<or> ?z b = True"})
  val negated_conjecture = Skip_Proof.make_thm @{theory} @{prop "(a :: 'a) \<noteq> b"}
  val f = Jeha.try_saturate @{context} [leibniz, negated_conjecture]
\<close>
*)

lemma paper_example_25:
  shows "(\<And>z. z a \<Longrightarrow> z b) \<Longrightarrow> a = b"
  (* sledgehammer *)
  (* by metis (* fails *) *)
  using [[show_types=false, ML_print_depth=100, ML_exception_trace, jeha_trace_archive, jeha_trace_forward_simp, jeha_trace_simp_steps, jeha_trace_inferred, jeha_trace_cheap_simp]]
  by jeha (* 300ms *)

(* attempt to reproduce failed: Pure.protectI from mirabelle.log *)
ML\<open>
  val t = Logic.mk_term (Term.dummy_pattern @{typ prop})
  val c = Thm.cterm_of @{context} t
  val g = Goal.init c
  val res = Jeha_Tactic.jeha_tac [] @{context} [] 0 g
  val first = Seq.pull res
\<close>

end