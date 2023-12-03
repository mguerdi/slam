theory paper_example_25

imports "test_base"

begin

declare [[jeha_trace]]

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

declare [[jeha_proof_reconstruction]]
*)

lemma paper_example_25:
  shows "(\<And>z. z a = True \<Longrightarrow> z b = True) \<Longrightarrow> a = b"
  by jeha

end