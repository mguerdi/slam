theory neg_ext

imports JEHA_TEST_BASE.test_base

begin

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b) = g \<Longrightarrow> \<not>D \<Longrightarrow> False"}
  val expected =
    mk @{prop "\<not>C' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b) (SOME x. f x \<noteq> g x) = g (SOME x. f x \<noteq> g x) \<Longrightarrow> \<not>D \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_neg_ext
      @{context}
      { premise = C, literal = 1 }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b) = (\<lambda>y. g y y) \<Longrightarrow> \<not>D \<Longrightarrow> False"}
  val expected =
    mk @{prop "\<not>C' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b) (SOME x. f x \<noteq> g x x) = g (SOME x. f x \<noteq> g x x) (SOME x. f x \<noteq> g x x) \<Longrightarrow> \<not>D \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_neg_ext
      @{context}
      { premise = C, literal = 1 }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

end