theory arg_cong

imports SLAM_TEST_BASE.test_base

begin

ML_val \<open>
  val C = mkh @{prop "\<not>C' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b \<Rightarrow> 'c) \<noteq> g \<Longrightarrow> \<not>D \<Longrightarrow> False"}
  val expected = mkh @{term_schem "\<not>C' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b \<Rightarrow> 'c) ?x ?y \<noteq> g ?x ?y \<Longrightarrow> \<not>D \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_arg_cong
      @{context}
      { premise = C, literal = 1, vars = [@{term_schem "?x :: 'a"}, @{term_schem "?y :: 'b"}] }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

end