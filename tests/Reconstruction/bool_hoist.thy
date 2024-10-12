theory bool_hoist

imports JEHA_TEST_BASE.test_base

begin

ML \<open>
  val mk = Skip_Proof.make_thm @{theory}
\<close>

ML_val \<open>
  val premise = mk @{prop "A \<Longrightarrow> B (b :: bool) = B' \<Longrightarrow> C \<Longrightarrow> False"}
  val expected = mk @{prop "A \<Longrightarrow> B False = B' \<Longrightarrow> C \<Longrightarrow> b \<noteq> True \<Longrightarrow> False"}
  val conclusion = Jeha_Proof.reconstruct_bool_hoist @{context} {premise = premise, subterm = ([1], JLit.Left, 1)}
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

ML_val \<open>
  val premise = mk @{prop "A \<Longrightarrow> B ((f c) :: bool) = B' \<Longrightarrow> C \<Longrightarrow> False"}
  val expected = mk @{prop "A \<Longrightarrow> B False = B' \<Longrightarrow> C \<Longrightarrow> f c \<noteq> True \<Longrightarrow> False"}
  val conclusion = Jeha_Proof.reconstruct_bool_hoist @{context} {premise = premise, subterm = ([1], JLit.Left, 1)}
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

end