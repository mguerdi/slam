theory paper_example_26

imports "SLAM.slam" HOL.Sledgehammer 

begin

lemma paper_example_26_all_rules:
  shows "(\<exists> y. \<forall> x . y x = (p x \<and> q x))"
  (* sledgehammer suggests only: *)
  (* by moura (* 5 ms *) *)
  by (slam) (* 34 ms *)
  (* using [[slam_meson, slam_max_number_of_steps=1000]] by (slam) (* doesn't work *) *)

(* Faithful reproduction of the proof of example 26 in the paper. *)

declare [[slam_disable_all]]

declare [[slam_rule_forall_rw]]
declare [[slam_rule_exists_hoist]]
declare [[slam_rule_bool_rw]]
declare [[slam_rule_simp_false_elim]]

lemma paper_example_26_restricted:
  shows "(\<exists> y. \<forall> x . y x = (p x \<and> q x))"
  using [[slam_trace]] by slam (* 16 ms *)

end