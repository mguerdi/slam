theory paper_example_25

imports JEHA_TEST_BASE.test_base

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
  by jeha (* 19 ms *)

(* Slightly closer to the proof of example 25 from the paper. *)
declare [[jeha_disable_all]]

declare [[jeha_rule_eq_hoist]]
declare [[jeha_rule_bool_rw]]
declare [[jeha_rule_false_elim]]
declare [[jeha_rule_sup]]
declare [[jeha_rule_e_res]]

(* To reach the initial clause set of example 25. *)
declare [[jeha_rule_simp_outer_claus]]

(* necessary *)
declare [[jeha_rule_clause_subsumption]]

declare [[jeha_rule_simp_bool_rw]]
declare [[jeha_rule_simp_false_elim]]

lemma paper_example_25:
  shows "(\<And>z. z a \<Longrightarrow> z b) \<Longrightarrow> a = b"
  by jeha (* 167ms *)

end