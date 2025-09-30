theory dd

imports "SLAM_TEST_BASE.test_base"

begin

ML \<open>
  fun mk t = { th = Skip_Proof.make_thm @{theory} t, skolems = [] }
  fun eq_thm ({ th = th1, ... }: HClause.hthm, { th = th2, ...}: HClause.hthm) =
    Thm.eq_thm_prop (th1, th2)
\<close>

ML_val \<open>
  val C = mk @{prop "A \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val expected = mk @{prop "A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C, duplicate_cposs = [{duplicate_of = 0, duplicate = 1, orientation = JLit.Left}] }
  val () = \<^assert> (eq_thm (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C, duplicate_cposs = [{duplicate_of = 1, duplicate = 2, orientation = JLit.Left}] }
  val () = \<^assert> (eq_thm (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<Longrightarrow> C \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C, duplicate_cposs = [{duplicate_of = 1, duplicate = 3, orientation = JLit.Left}] }
  val () = \<^assert> (eq_thm (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C
      , duplicate_cposs =
        [ { duplicate_of = 1, duplicate = 3, orientation = JLit.Left }
        , { duplicate_of = 2, duplicate = 4, orientation = JLit.Left} ] }
  val () = \<^assert> (eq_thm (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B \<Longrightarrow> A \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C
      , duplicate_cposs =
        [ { duplicate_of = 1, duplicate = 4, orientation = JLit.Left }
        , { duplicate_of = 2, duplicate = 3, orientation = JLit.Left } ] }
  val () = \<^assert> (eq_thm (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B \<Longrightarrow> A \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C
      , duplicate_cposs =
        [ { duplicate_of = 2, duplicate = 3, orientation = JLit.Left }
        , { duplicate_of = 1, duplicate = 4, orientation = JLit.Left } ] }
  val () = \<^assert> (eq_thm (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C
      , duplicate_cposs =
        [ { duplicate_of = 3, duplicate = 4, orientation = JLit.Left }
        , { duplicate_of = 1, duplicate = 2, orientation = JLit.Left } ] }
  val () = \<^assert> (eq_thm (expected, conclusion))
\<close>

end