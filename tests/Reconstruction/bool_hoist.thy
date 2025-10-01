theory bool_hoist

imports SLAM_TEST_BASE.test_base

begin

ML_val \<open>
  val premise = mkh @{prop "A \<Longrightarrow> B (b :: bool) = B' \<Longrightarrow> C \<Longrightarrow> False"}
  val expected = mkh @{prop "A \<Longrightarrow> B False = B' \<Longrightarrow> C \<Longrightarrow> b \<noteq> True \<Longrightarrow> False"}
  val conclusion = Slam_Proof.reconstruct_bool_hoist @{context} {premise = premise, subterm = ([1], JLit.Left, 1)}
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

ML_val \<open>
  val premise = mkh @{prop "A \<Longrightarrow> B ((f c) :: bool) = B' \<Longrightarrow> C \<Longrightarrow> False"}
  val expected = mkh @{prop "A \<Longrightarrow> B False = B' \<Longrightarrow> C \<Longrightarrow> f c \<noteq> True \<Longrightarrow> False"}
  val conclusion = Slam_Proof.reconstruct_bool_hoist @{context} {premise = premise, subterm = ([1], JLit.Left, 1)}
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

end