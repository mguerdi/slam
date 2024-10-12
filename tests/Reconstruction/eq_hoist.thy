theory eq_hoist

imports "JEHA_TEST_BASE.test_base"

begin

ML \<open>
  val mk = Skip_Proof.make_thm @{theory}
\<close>

ML_val \<open>
  val premise = mk @{prop "A \<Longrightarrow> B (c = d) = E \<Longrightarrow> F \<Longrightarrow> False"}
  val expected = mk @{prop "A \<Longrightarrow> B False = E \<Longrightarrow> F \<Longrightarrow> c \<noteq> d \<Longrightarrow> False"}
  val conclusion = Jeha_Proof.reconstruct_eq_hoist @{context} { premise = premise, subterm = ([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

end 