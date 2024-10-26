theory positive_simplify_reflect

imports JEHA_TEST_BASE.test_base

begin

ML_val \<open>
  val unit = mk @{prop "(a :: 'a) \<noteq> b \<Longrightarrow> False"}
  val C = mk @{prop "\<not>C' \<Longrightarrow> u (a :: 'a) c = u b c \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_positive_simplify_reflect
      @{context}
      { unit = unit
      , unit_orientation = JLit.Left
      , right_premise = C
      , disagreement = ([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

ML_val \<open>
  val unit = mk @{prop "(b :: 'a) \<noteq> a \<Longrightarrow> False"}
  val C = mk @{prop "\<not>C' \<Longrightarrow> u (a :: 'a) c = u b c \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_positive_simplify_reflect
      @{context}
      { unit = unit
      , unit_orientation = JLit.Right
      , right_premise = C
      , disagreement = ([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

ML_val \<open>
  val unit = mk @{prop "(b :: 'a) \<noteq> a \<Longrightarrow> False"}
  val C = mk @{prop "\<not>C' \<Longrightarrow> u (a :: 'a) c = u b c \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>C' \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_positive_simplify_reflect
      @{context}
      { unit = unit
      , unit_orientation = JLit.Left
      , right_premise = C
      , disagreement = ([1], JLit.Right, 1) }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

end