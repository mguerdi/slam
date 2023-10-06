theory paper_example_26

imports "../jeha" 

begin

declare [[jeha_trace]]

declare [[jeha_disable_all]]

declare [[jeha_rule_forall_rw]]
declare [[ jeha_rule_exists_hoist ]]
declare [[ jeha_rule_bool_rw ]]
declare [[ jeha_rule_false_elim ]]

(* NOTE: Example 26 in the paper doesn't work out of the box: FalseElim doesn't
handle True = False \<or> True = False, because neither literal is strictly maximal.
In Addition EFact and ERes are required (or selection functions). *)
declare [[jeha_rule_e_fact]]
declare [[jeha_rule_e_res]]

declare [[jeha_proof_reconstruction]]
declare [[metis_trace]]

lemma paper_example_26:
  shows "(\<exists> y. \<forall> x . y x = (p x \<and> q x)) \<noteq> False"
  by (jeha)

end