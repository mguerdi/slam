theory paper_example_25

imports "JEHA.jeha_debug"

begin

declare [[jeha_trace]]

lemma paper_example_25_all_rules:
  shows "(\<And>z. z a \<Longrightarrow> z b) \<Longrightarrow> a = b"
  (* by metis (* fails *) *)
  using [[jeha_proof_reconstruction, metis_trace, (* show_types, ML_print_depth=100, ML_exception_trace, jeha_trace_archive, *) jeha_trace_forward_simp, jeha_trace_simp_steps (* jeha_trace_inferred, jeha_trace_cheap_simp *)]]
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

(* fails with exception
  forall_intr: variable "x" free in assumptions

*)
declare [[jeha_proof_reconstruction]]

lemma paper_example_25:
  shows "(\<And>z. z a \<Longrightarrow> z b) \<Longrightarrow> a = b"
  (* sledgehammer *)
  (* by metis (* fails *) *)
  using [[show_types, ML_print_depth=100, ML_exception_trace, jeha_trace_archive, jeha_trace_forward_simp, jeha_trace_simp_steps, jeha_trace_inferred, jeha_trace_cheap_simp]]
  by jeha (* 300ms *)

end