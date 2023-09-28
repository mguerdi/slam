theory paper_example_26

imports "../jeha" 

begin

declare [[jeha_trace]]

declare [[jeha_disable_all]]

declare [[jeha_rule_forall_rw]]
declare [[ jeha_rule_exists_hoist ]]
declare [[ jeha_rule_bool_rw ]]
declare [[ jeha_rule_false_elim ]]

declare [[jeha_rule_e_fact]]
declare [[jeha_rule_e_res]]

(* doesn't work without smash unifiers: *)
(* declare [[jeha_disable_smash_unifiers]] *)


lemma paper_example_26:
  shows "(\<exists> y. \<forall> x . y x = (p x \<and> q x)) \<noteq> False"
  by (jeha)

end