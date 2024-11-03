theory efact

imports JEHA_TEST_BASE.test_base

begin

ML \<open>
  val mk = Skip_Proof.make_thm @{theory}
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> u \<noteq> v' \<Longrightarrow> u \<noteq> v \<Longrightarrow> False"}
  (* Expect: v \<noteq> v' \<Longrightarrow> u = v' \<Longrightarrow> \<not>C' \<Longrightarrow> False *)
  val expected = mk @{prop "\<not>C' \<Longrightarrow> v = v' \<Longrightarrow> (u :: 'a) \<noteq> v' \<Longrightarrow> False"}
  val conclusion = Jeha_Proof.reconstruct_efact
    { left_literal = (JLit.Left, 1), right_literal = (JLit.Left, 2), premise = C }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

ML_val \<open>
  val C_four_lits = mk @{prop "A \<Longrightarrow> B \<Longrightarrow> (u :: 'a) \<noteq> v' \<Longrightarrow> u \<noteq> v \<Longrightarrow> False"}
  val expected_four_lits = mk @{prop "A \<Longrightarrow> B \<Longrightarrow> v = v' \<Longrightarrow> (u :: 'a) \<noteq> v' \<Longrightarrow> False"}
  val conclusion_four_lits = Jeha_Proof.reconstruct_efact
    { left_literal = (JLit.Left, 2), right_literal = (JLit.Left, 3), premise = C_four_lits }
  val () = \<^assert> (Thm.eq_thm_prop (expected_four_lits, conclusion_four_lits))
\<close>

ML_val \<open>
  val C3 = mk @{prop "\<not>C' \<Longrightarrow> v' \<noteq> u \<Longrightarrow> u \<noteq> v \<Longrightarrow> False"}
  val expected3 = mk @{prop "\<not>C' \<Longrightarrow> v = v' \<Longrightarrow> (u :: 'a) \<noteq> v' \<Longrightarrow> False"}
  val conclusion3 = Jeha_Proof.reconstruct_efact
    { left_literal = (JLit.Right, 1), right_literal = (JLit.Left, 2), premise = C3 }
  val () = \<^assert> (Thm.eq_thm_prop (expected3, conclusion3))
\<close>

(* FIXME integrate tests with jeha.ML *)

end