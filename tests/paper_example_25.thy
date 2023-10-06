theory paper_example_25

imports "../jeha" 

begin

declare [[jeha_trace]]

declare [[jeha_disable_all]]

declare [[jeha_rule_eq_hoist]]
declare [[jeha_rule_bool_rw]]
declare [[jeha_rule_false_elim]]
declare [[jeha_rule_sup]]
declare [[jeha_rule_e_res]]

declare [[jeha_rule_forall_hoist]]

(* declare [[jeha_proof_reconstruction]] *)

lemma paper_example_25:
  shows "(\<And>z. z a = True \<Longrightarrow> z b = True) \<Longrightarrow> a = b"
  by (jeha)

end