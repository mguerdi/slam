theory false_elim

imports "SLAM_TEST_BASE.test_base"

begin

ML_val \<open>
  val premise = mkh @{prop "\<not>C' \<Longrightarrow> False \<noteq> True \<Longrightarrow> False"}
  val expected = mkh @{prop "\<not>C' \<Longrightarrow> False"}
  val conclusion = Slam_Proof.reconstruct_false_elim @{context} { premise = premise, literal = (JLit.Left, 1) }
  val () = \<^assert> (eqh (conclusion, expected))
\<close>

ML_val \<open>
  val premise = mkh @{prop "A \<Longrightarrow> False \<noteq> True \<Longrightarrow> B \<Longrightarrow> False"}
  val expected = mkh @{prop "A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion = Slam_Proof.reconstruct_false_elim @{context} { premise = premise, literal = (JLit.Left, 1) }
  val () = \<^assert> (eqh (conclusion, expected))
\<close>

end