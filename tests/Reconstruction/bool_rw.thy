theory bool_rw

imports SLAM_TEST_BASE.test_base

begin

ML_val \<open>
  val premise = mkh @{prop "(\<not>True) \<noteq> False \<Longrightarrow> False"}
  val expected = mkh @{prop "False \<noteq> False \<Longrightarrow> False"}
  val subrule =
    HClause.of_lemma (Slam_Lemma.hclause_of_uninstantiated_bool_rw_rule @{context} (@{term "\<not>True"}, @{term "False"}))
  val conclusion =
    Slam_Proof.reconstruct_bool_rw
      @{context}     
      { premise = premise
      , subterm = ([], JLit.Left, 0)
      , instantiated_subrule = subrule }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

ML_val \<open>
  val premise = mkh @{prop "((b :: 'b) = b) \<noteq> C \<Longrightarrow> False"}
  val expected = mkh @{prop "True \<noteq> C \<Longrightarrow> False"}
  val subrule =
    (@{term_schem "(?y :: ?'a) = ?y"}, @{term_schem "True"})
    |> Slam_Lemma.hclause_of_uninstantiated_bool_rw_rule @{context}
    |> Thm.instantiate' [SOME @{ctyp "'b"}] [SOME @{cterm "b :: 'b"}]
    |> HClause.of_lemma
  val ctxt = @{context}
  val subterm = ([], JLit.Left, 0)
  val conclusion =
    Slam_Proof.reconstruct_bool_rw
      ctxt
      { premise = premise
      , subterm = subterm
      , instantiated_subrule = subrule }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

ML_val \<open>
  val premise = mkh @{prop "((b :: 'b) \<noteq> b) \<noteq> C \<Longrightarrow> False"}
  val expected = mkh @{prop "False \<noteq> C \<Longrightarrow> False"}
  val subrule =
    (@{term_schem "(?y :: ?'a) \<noteq> ?y"}, @{term_schem "False"})
    |> Slam_Lemma.hclause_of_uninstantiated_bool_rw_rule @{context}
    |> Thm.instantiate' [SOME @{ctyp "'b"}] [SOME @{cterm "b :: 'b"}]
    |> HClause.of_lemma
  val ctxt = @{context}
  val subterm = ([], JLit.Left, 0)
  val conclusion =
    Slam_Proof.reconstruct_bool_rw
      ctxt
      { premise = premise
      , subterm = subterm
      , instantiated_subrule = subrule }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

end