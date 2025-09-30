theory dd

imports "SLAM_TEST_BASE.test_base"

begin

(*
(* If every predicate that distinguishes c and d is constant, then c and d must be equal *)
lemma "(\<And>(P :: 'a \<Rightarrow> bool). P c \<noteq> P d \<Longrightarrow> \<exists>y. \<forall>x. y = P x) \<Longrightarrow> c = d"
  using [[slam_trace]] by slam (* this had a reconstruction bug *)
*)

ML_val \<open>
  val C = mkh @{term_schem "?P c \<noteq> ?P d \<Longrightarrow> ?P c \<noteq> ?P d \<Longrightarrow> ?P ?x3 \<noteq> ?P ?x1 \<Longrightarrow> False"}
  val expected = mkh @{term_schem "?P c \<noteq> ?P d \<Longrightarrow> ?P ?x3 \<noteq> ?P ?x1 \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C, duplicate_cposs = [{duplicate = 1, duplicate_of = 0, orientation = JLit.Left}] }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

ML_val \<open>
  val C = mkh @{prop "A \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val expected = mkh @{prop "A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C, duplicate_cposs = [{duplicate_of = 0, duplicate = 1, orientation = JLit.Left}] }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

ML_val \<open>
  val C = mkh @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> False"}
  val expected = mkh @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C, duplicate_cposs = [{duplicate_of = 1, duplicate = 2, orientation = JLit.Left}] }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

ML_val \<open>
  val C = mkh @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<Longrightarrow> C \<Longrightarrow> False"}
  val expected = mkh @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C, duplicate_cposs = [{duplicate_of = 1, duplicate = 3, orientation = JLit.Left}] }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

ML_val \<open>
  val C = mkh @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val expected = mkh @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C
      , duplicate_cposs =
        [ { duplicate_of = 1, duplicate = 3, orientation = JLit.Left }
        , { duplicate_of = 2, duplicate = 4, orientation = JLit.Left} ] }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

ML_val \<open>
  val C = mkh @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B \<Longrightarrow> A \<Longrightarrow> False"}
  val expected = mkh @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C
      , duplicate_cposs =
        [ { duplicate_of = 1, duplicate = 4, orientation = JLit.Left }
        , { duplicate_of = 2, duplicate = 3, orientation = JLit.Left } ] }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

ML_val \<open>
  val C = mkh @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B \<Longrightarrow> A \<Longrightarrow> False"}
  val expected = mkh @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C
      , duplicate_cposs =
        [ { duplicate_of = 2, duplicate = 3, orientation = JLit.Left }
        , { duplicate_of = 1, duplicate = 4, orientation = JLit.Left } ] }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

ML_val \<open>
  val C = mkh @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> B \<Longrightarrow> False"}
  val expected = mkh @{prop "\<not>C' \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_delete_duplicated_lits
      { premise = C
      , duplicate_cposs =
        [ { duplicate_of = 3, duplicate = 4, orientation = JLit.Left }
        , { duplicate_of = 1, duplicate = 2, orientation = JLit.Left } ] }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

end