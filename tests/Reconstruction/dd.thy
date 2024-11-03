theory dd

imports "JEHA_TEST_BASE.test_base"

begin

ML_val \<open>
  val C = mk @{prop "A \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val expected = mk @{prop "A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_delete_duplicated_lits
      { premise = C, duplicate_cposs = [{duplicate_of = 0, duplicate = 1}] }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_delete_duplicated_lits
      { premise = C, duplicate_cposs = [{duplicate_of = 1, duplicate = 2}] }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<Longrightarrow> C \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_delete_duplicated_lits
      { premise = C, duplicate_cposs = [{duplicate_of = 1, duplicate = 3}] }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_delete_duplicated_lits
      { premise = C
      , duplicate_cposs =
        [ { duplicate_of = 1, duplicate = 3 }
        , { duplicate_of = 2, duplicate = 4 } ] }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B \<Longrightarrow> A \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_delete_duplicated_lits
      { premise = C
      , duplicate_cposs =
        [ { duplicate_of = 1, duplicate = 4 }
        , { duplicate_of = 2, duplicate = 3 } ] }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B \<Longrightarrow> A \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_delete_duplicated_lits
      { premise = C
      , duplicate_cposs =
        [ { duplicate_of = 2, duplicate = 3 }
        , { duplicate_of = 1, duplicate = 4 } ] }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_delete_duplicated_lits
      { premise = C
      , duplicate_cposs =
        [ { duplicate_of = 3, duplicate = 4 }
        , { duplicate_of = 1, duplicate = 2 } ] }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

end