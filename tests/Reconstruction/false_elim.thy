theory false_elim

imports "JEHA_TEST_BASE.test_base"

begin

ML \<open>
  val mk = Skip_Proof.make_thm @{theory}
\<close>

ML_val \<open>
  val premise = mk @{prop "\<not>C' \<Longrightarrow> False \<noteq> True \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> False"}
  val conclusion = Jeha_Proof.reconstruct_false_elim @{context} { premise = premise, literal = (JLit.Left, 1) }
  val () = \<^assert> (Thm.eq_thm_prop (conclusion, expected))
\<close>

ML_val \<open>
  val premise = mk @{prop "A \<Longrightarrow> False \<noteq> True \<Longrightarrow> B \<Longrightarrow> False"}
  val expected = mk @{prop "A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion = Jeha_Proof.reconstruct_false_elim @{context} { premise = premise, literal = (JLit.Left, 1) }
  val () = \<^assert> (Thm.eq_thm_prop (conclusion, expected))
\<close>

end