theory paper_example_26

imports "../jeha" 

begin

declare [[jeha_trace]]

(* lemma paper_example_26_all_rules:
  shows "(\<exists> y. \<forall> x . y x = (p x \<and> q x))"
  (* sledgehammer *)
  (* by metis (* fails *) *)
  using [[jeha_trace_active]] by (jeha) (* 80_000 ms *) *)

declare [[jeha_disable_all]]

declare [[jeha_rule_forall_rw]]
declare [[jeha_rule_exists_hoist]]
declare [[jeha_rule_bool_rw]]
declare [[jeha_rule_false_elim]]

(* NOTE: Example 26 in the paper doesn't work out of the box: FalseElim doesn't
handle True = False \<or> True = False, because neither literal is strictly maximal.
In Addition EFact and ERes are required (or selection functions). *)
declare [[jeha_rule_e_fact]]
declare [[jeha_rule_e_res]]

(* necessary, because the contradiction is
  False = True \<or> False = True
but FalseElim doesn't apply because of its strict-maximality side condition *)
declare [[jeha_rule_simp_false_elim]]

(* works but takes very long (> 1 min): *)
declare [[jeha_proof_reconstruction]]
declare [[metis_trace]]

lemma paper_example_26:
  shows "(\<exists> y. \<forall> x . y x = (p x \<and> q x))"
  (* sledgehammer
  by metis *)
  by (jeha) (* 29500 ms *)

end