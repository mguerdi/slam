theory eres

imports JEHA_TEST_BASE.test_base

begin

ML \<open>
  val mk = Skip_Proof.make_thm @{theory}
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C \<Longrightarrow> u = u \<Longrightarrow> A \<Longrightarrow> False"}
  val D = Jeha_Proof.reconstruct_eres {premise = C, literal = 1}
  val expected = mk @{prop "\<not>C \<Longrightarrow> A \<Longrightarrow> False"}
  val () = \<^assert> (Thm.eq_thm_prop (D, expected))
\<close>

ML_val \<open>
  val C = mk @{prop "u = u \<Longrightarrow> False"}
  val D = Jeha_Proof.reconstruct_eres {premise = C, literal = 0}
  val expected = mk @{prop "False"}
  val () = \<^assert> (Thm.eq_thm_prop (D, expected))
\<close>

end