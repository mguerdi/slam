theory bool_exhaustive

imports SLAM_TEST_BASE.test_base HOL.Sledgehammer

begin

lemma "True = False \<or> True = False \<Longrightarrow> False"
  using [[slam_trace,
        slam_trace_e_fact,
        slam_disable_all,
        slam_rule_bool_hoist,
        slam_rule_sup,
        slam_rule_false_elim,
        slam_rule_e_fact,
        slam_rule_e_res,
        slam_rule_clause_subsumption
  ]] by slam

lemma "f True \<Longrightarrow> f False \<Longrightarrow> f x"
  using [[slam_trace,
        (* slam_trace_sup,
        slam_trace_e_fact, *)
        slam_disable_all,
        slam_rule_bool_hoist,
        slam_rule_sup,
        slam_rule_false_elim,
        slam_rule_e_fact,
        slam_rule_e_res,
        slam_rule_clause_subsumption
   ]] by slam

thm ext[of "f" "\<lambda>x. x"]

lemma to_ext: "(f = g) = (\<forall>x. f x = g x)"
  by auto

lemma exhaust: "(\<forall>x. f x = g x) = ((f True = g True) \<and> (f False = g False))"
proof
  show "f True = g True \<and> f False = g False \<Longrightarrow> \<forall>x. f x = g x"
  proof
    fix x
    assume "(f True = g True) \<and> (f False = g False)"
    then have "f True = g True" and "f False = g False" by auto
    then show "f x = g x" by (rule bool_induct)
  qed
  show "\<forall>x. f x = g x \<Longrightarrow> f True = g True \<and> f False = g False" by auto
qed

lemma "f = (\<lambda>x. x) \<or> f = (\<lambda>x. \<not>x) \<or> f = (\<lambda>x. True) \<or> f = (\<lambda>x. False)"
  (* (* works: *) by metis *)
  by slam

end