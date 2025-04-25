theory proof_util

imports JEHA_TEST_BASE.test_base

begin

ML \<open>
  val mk = Skip_Proof.make_thm @{theory}
\<close>

ML_val \<open>
  val C = mk @{prop "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E"}
  val expected = mk @{prop "B \<Longrightarrow> C \<Longrightarrow> A \<Longrightarrow> D \<Longrightarrow> E"}
  val actual = Jeha_Proof_Util.move_prems_left 2 2 1 C
  val () = \<^assert> (Thm.eq_thm (expected, actual))
\<close>

ML_val \<open>
  val C = mk @{prop "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E"}
  val expected = mk @{prop "A \<Longrightarrow> C \<Longrightarrow> B \<Longrightarrow> D \<Longrightarrow> E"}
  val actual = Jeha_Proof_Util.move_prems_left 3 1 1 C
  val () = \<^assert> (Thm.eq_thm (expected, actual))
\<close>

ML_val \<open>
  val C = mk @{prop "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E"}
  val expected = mk @{prop "C \<Longrightarrow> D \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> E"}
  val actual = Jeha_Proof_Util.move_prems_left 3 2 2 C
  val () = \<^assert> (Thm.eq_thm (expected, actual))
\<close>

end