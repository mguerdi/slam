theory dr

imports JEHA_TEST_BASE.test_base

begin

ML_val \<open>
  val premise =
    mk @{term_schem "A \<Longrightarrow> (\<lambda>x. B x (?c :: ?'c)) = (\<lambda>x. B x ?c) \<Longrightarrow> C \<Longrightarrow> d = d \<Longrightarrow> E \<Longrightarrow> False"}
  val expected = mk @{term_schem "A \<Longrightarrow> C \<Longrightarrow> E \<Longrightarrow> False"}
  val conclusion = Jeha_Proof.reconstruct_delete_resolved_lits { premise = premise, cposs = [1, 3] }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

end