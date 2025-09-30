theory forall_rw

imports SLAM_TEST_BASE.test_base

begin

(* FIXME: need a new strategy for testing these *)
ML_val \<open>
  val premise = mkh @{prop "A \<Longrightarrow> B (\<forall>x. (Q :: 'b \<Rightarrow> 'c \<Rightarrow> bool) x c) = B' \<Longrightarrow> False"}
  val expected = mkh @{prop "A \<Longrightarrow> B ((Q :: 'b \<Rightarrow> 'c \<Rightarrow> bool) (SOME x. \<not> Q x c) c) = B' \<Longrightarrow> False"}
  val predicate = @{cterm "\<lambda>x. (Q :: 'b \<Rightarrow> 'c \<Rightarrow> bool) x c"}
  val subterm = ([1], JLit.Left, 1)
  val conclusion =
    Slam_Proof.reconstruct_forall_rw
      @{context}
      { premise = premise, subterm = subterm, predicate = predicate }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

end