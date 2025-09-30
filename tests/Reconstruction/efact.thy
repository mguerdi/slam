theory efact

imports SLAM_TEST_BASE.test_base

begin

ML_val \<open>
  val C = mkh @{prop "\<not>C' \<Longrightarrow> u \<noteq> v' \<Longrightarrow> u \<noteq> v \<Longrightarrow> False"}
  (* Expect: v \<noteq> v' \<Longrightarrow> u = v' \<Longrightarrow> \<not>C' \<Longrightarrow> False *)
  val expected = mkh @{prop "\<not>C' \<Longrightarrow> v = v' \<Longrightarrow> (u :: 'a) \<noteq> v' \<Longrightarrow> False"}
  val conclusion = Slam_Proof.reconstruct_efact
    { left_literal = (JLit.Left, 1), right_literal = (JLit.Left, 2), premise = C }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

ML_val \<open>
  val C_four_lits = mkh @{prop "A \<Longrightarrow> B \<Longrightarrow> (u :: 'a) \<noteq> v' \<Longrightarrow> u \<noteq> v \<Longrightarrow> False"}
  val expected_four_lits = mkh @{prop "A \<Longrightarrow> B \<Longrightarrow> v = v' \<Longrightarrow> (u :: 'a) \<noteq> v' \<Longrightarrow> False"}
  val conclusion_four_lits = Slam_Proof.reconstruct_efact
    { left_literal = (JLit.Left, 2), right_literal = (JLit.Left, 3), premise = C_four_lits }
  val () = \<^assert> (eqh (expected_four_lits, conclusion_four_lits))
\<close>

ML_val \<open>
  val C3 = mkh @{prop "\<not>C' \<Longrightarrow> v' \<noteq> u \<Longrightarrow> u \<noteq> v \<Longrightarrow> False"}
  val expected3 = mkh @{prop "\<not>C' \<Longrightarrow> v = v' \<Longrightarrow> (u :: 'a) \<noteq> v' \<Longrightarrow> False"}
  val conclusion3 = Slam_Proof.reconstruct_efact
    { left_literal = (JLit.Right, 1), right_literal = (JLit.Left, 2), premise = C3 }
  val () = \<^assert> (eqh (expected3, conclusion3))
\<close>

(* FIXME integrate tests with slam.ML *)

end