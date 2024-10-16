theory bool_rw

imports JEHA_TEST_BASE.test_base

begin

ML \<open>
  val mk = Skip_Proof.make_thm @{theory}
\<close>

ML_val \<open>
  val premise = mk @{prop "(\<not>True) \<noteq> False \<Longrightarrow> False"}
  val expected = mk @{prop "False \<noteq> False \<Longrightarrow> False"}
  val subrule =
    Jeha_Lemma.hclause_of_uninstantiated_bool_rw_rule @{context} (@{term "\<not>True"}, @{term "False"})
  val conclusion =
    Jeha_Proof.reconstruct_bool_rw
      @{context}     
      { premise = premise
      , subterm = ([], JLit.Left, 0)
      , subrule = subrule }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

ML_val \<open>
  val premise = mk @{prop "((b :: 'b) = b) \<noteq> C \<Longrightarrow> False"}
  val expected = mk @{prop "True \<noteq> C \<Longrightarrow> False"}
  val subrule =
    (@{term_schem "(?y :: ?'a) = ?y"}, @{term_schem "True"})
    |> Jeha_Lemma.hclause_of_uninstantiated_bool_rw_rule @{context}
    |> Thm.instantiate' [SOME @{ctyp "'b"}] [SOME @{cterm "b :: 'b"}]
  val ctxt = @{context}
  val subterm = ([], JLit.Left, 0)
  val conclusion =
    Jeha_Proof.reconstruct_bool_rw
      ctxt
      { premise = premise
      , subterm = subterm
      , subrule = subrule }
\<close>

ML_val \<open>
  val premise = mk @{prop "((b :: 'b) \<noteq> b) \<noteq> C \<Longrightarrow> False"}
  val expected = mk @{prop "False \<noteq> C \<Longrightarrow> False"}
  val subrule =
    (@{term_schem "(?y :: ?'a) \<noteq> ?y"}, @{term_schem "False"})
    |> Jeha_Lemma.hclause_of_uninstantiated_bool_rw_rule @{context}
    |> Thm.instantiate' [SOME @{ctyp "'b"}] [SOME @{cterm "b :: 'b"}]
  val ctxt = @{context}
  val subterm = ([], JLit.Left, 0)
  val conclusion =
    Jeha_Proof.reconstruct_bool_rw
      ctxt
      { premise = premise
      , subterm = subterm
      , subrule = subrule }
\<close>

end