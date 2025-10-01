theory eres

imports SLAM_TEST_BASE.test_base

begin

ML_val \<open>
  val C = mkh @{prop "\<not>C \<Longrightarrow> u = u \<Longrightarrow> A \<Longrightarrow> False"}
  val D = Slam_Proof.reconstruct_eres {premise = C, literal = 1}
  val expected = mkh @{prop "\<not>C \<Longrightarrow> A \<Longrightarrow> False"}
  val () = \<^assert> (eqh (D, expected))
\<close>

ML_val \<open>
  val C = mkh @{prop "u = u \<Longrightarrow> False"}
  val D = Slam_Proof.reconstruct_eres {premise = C, literal = 0}
  val expected = mkh @{prop "False"}
  val () = \<^assert> (eqh (D, expected))
\<close>

end