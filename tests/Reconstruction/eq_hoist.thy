theory eq_hoist

imports "SLAM_TEST_BASE.test_base"

begin

ML_val \<open>
  val premise = mkh @{prop "A \<Longrightarrow> B (c = d) = E \<Longrightarrow> F \<Longrightarrow> False"}
  val expected = mkh @{prop "A \<Longrightarrow> B False = E \<Longrightarrow> F \<Longrightarrow> c \<noteq> d \<Longrightarrow> False"}
  val conclusion = Slam_Proof.reconstruct_eq_hoist @{context} { premise = premise, subterm = ([1], JLit.Left, 1) }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

end 