theory positive_simplify_reflect

imports SLAM.slam

begin

lemma "a = b \<Longrightarrow> u a c \<noteq> u b c \<or> C \<Longrightarrow> C"
  using [[slam_trace, slam_disable_all,
        slam_rule_positive_simplify_reflect, slam_rule_sup, slam_rule_false_elim]]
  by slam

end