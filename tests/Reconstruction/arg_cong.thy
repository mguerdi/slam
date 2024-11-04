theory arg_cong

imports JEHA_TEST_BASE.test_base

begin

ML_val \<open>
  val C = mk @{prop "\<not>C' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b \<Rightarrow> 'c) \<noteq> g \<Longrightarrow> \<not>D \<Longrightarrow> False"}
  val expected = mk @{term_schem "\<not>C' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b \<Rightarrow> 'c) ?x ?y \<noteq> g ?x ?y \<Longrightarrow> \<not>D \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_arg_cong
      @{context}
      { premise = C, literal = 1, vars = [@{term_schem "?x :: 'a"}, @{term_schem "?y :: 'b"}] }
  val () = \<^assert> (Thm.eq_thm_prop (expected, conclusion))
\<close>

end