theory sup

imports "SLAM.slam" HOL.HOL

begin

declare [[slam_trace]]

declare [[slam_disable_all]]
declare [[slam_rule_sup]]
declare [[slam_rule_e_res]]
declare [[slam_rule_e_fact]]

lemma transitivity:
  shows "x = y \<Longrightarrow> y = z \<Longrightarrow> x = z"
  by (slam) (* 8 ms *)

lemma congruence:
  shows "x = y \<Longrightarrow> f x = f y"
  by (slam) (* 5 ms *)

lemma deep_congruence:
  shows "x = y \<Longrightarrow> v = w  \<Longrightarrow> f (g (h x) w) = f (g (h y) v)"
  by (slam) (* 6 ms *)

lemma beta_reduction:
  shows "ev = (\<lambda> g x. g x) \<Longrightarrow> f = (\<lambda> x. x) \<Longrightarrow> ev f x = x"
  using [[slam_rule_clause_subsumption, slam_rule_arg_cong]] by slam (* 49 ms *)

end
