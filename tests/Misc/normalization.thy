theory normalization

imports "SLAM_TEST_BASE.test_base"

begin

declare [[show_types]]

ML \<open>
  val Ta = @{typ "'a"};
  val b = @{term "b :: 'a"};
  val f = @{term "f :: ('b \<Rightarrow> HOL.bool) \<Rightarrow> 'a \<Rightarrow> HOL.bool"};
  val t = HOLogic.all_const Ta $ (f $ Abs ("x", @{typ "'b"}, (HOLogic.all_const Ta $ (HOLogic.eq_const Ta $ b))));
  val t_normed = JTerm.norm_beta_eta_qeta_env (Envir.init) t;
  val t_expected = HOLogic.all_const Ta $ (Abs ("y", Ta, (f $ Abs ("x", @{typ "'b"}, (HOLogic.all_const Ta $ Abs ("z", Ta, (HOLogic.eq_const Ta $ b $ Bound 0)))) $ Bound 0)))
  val () = \<^assert> (t_expected aconv t_normed)
\<close>

ML \<open>
  val t = @{term        "((\<forall>(x::bool). ((\<lambda>(a::bool). (All ((=) a))) = (\<lambda>(a::bool). x))       ) = False)"};
  val t_normed = JTerm.norm_beta_eta_qeta_env (Envir.init) t;
  val t_expected = @{term        "((\<forall>(x::bool). ((\<lambda>(a::bool). (\<forall>y. a = y)) = (\<lambda>(a::bool). x))       ) = False)"};
  val () = \<^assert> (t_expected aconv t_normed)
\<close>

end
