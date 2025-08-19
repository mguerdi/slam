theory paper_example_26

imports "JEHA.jeha" HOL.Sledgehammer 

begin

lemma paper_example_26_all_rules:
  shows "(\<exists> y. \<forall> x . y x = (p x \<and> q x))"
  (* sledgehammer suggests only: *)
  (* by moura (* 5 ms *) *)
  by (jeha) (* 34 ms *)

(* Faithful reproduction of the proof of example 26 in the paper. *)

declare [[jeha_disable_all]]

declare [[jeha_rule_forall_rw]]
declare [[jeha_rule_exists_hoist]]
declare [[jeha_rule_bool_rw]]
declare [[jeha_rule_simp_false_elim]]

lemma paper_example_26_restricted:
  shows "(\<exists> y. \<forall> x . y x = (p x \<and> q x))"
  using [[jeha_trace]] by jeha (* 16 ms *)

end