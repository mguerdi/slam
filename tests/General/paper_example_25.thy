theory paper_example_25

imports SLAM_TEST_BASE.test_base

begin

lemma paper_example_25_all_rules:
  shows "(\<And>z. z a \<Longrightarrow> z b) \<Longrightarrow> a = b"
  (*
  sledgehammer
  (* only suggests this Isar proof: *)
  proof -
    assume "\<And>z. z a \<Longrightarrow> z b"
    then have "\<forall>p. p b \<or> \<not> p a"
      by blast
    then show ?thesis
      by blast
  qed
  *)
  using [[slam_trace]] by slam (* 19 ms *)

(* Slightly closer to the proof of example 25 from the paper. *)
declare [[slam_disable_all]]

declare [[slam_rule_eq_hoist=on]]
declare [[slam_rule_bool_rw=on]]
declare [[slam_rule_false_elim=on]]
declare [[slam_rule_sup=on]]
declare [[slam_rule_e_res=on]]

(* To reach the initial clause set of example 25. *)
declare [[slam_rule_simp_outer_claus=on]]

(* necessary *)
declare [[slam_rule_clause_subsumption=on]]

declare [[slam_rule_bool_simp=on]]
declare [[slam_rule_simp_false_elim=on]]
declare [[slam_rule_imitate_project=on]]
(* necessary with delayed simpl-only unification *)
declare [[slam_rule_delete_resolved_lits=on]]

lemma paper_example_25:
  shows "(\<And>z. z a \<Longrightarrow> z b) \<Longrightarrow> a = b"
  (* using [[slam_trace]] *)
  by slam (* 14ms *)

end