theory neg_ext

imports SLAM_TEST_BASE.test_base

begin

(* FIXME: need a new strategy for testing these *)

ML_val \<open>
  val C = mkh @{prop "\<not>C' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b) = g \<Longrightarrow> \<not>D \<Longrightarrow> False"}
  val choice_witness = @{term "(SOME x. (f :: 'a \<Rightarrow> 'b) x \<noteq> g x)"}
  val { skolem_constant, skolem_constant_with_args, skolem_constant_definition } =
    JTerm.make_skolem_constant choice_witness
  val sk_with_args_typ = Thm.ctyp_of @{context} (fastype_of skolem_constant_with_args)
  val sk_with_args = Thm.cterm_of @{context} skolem_constant_with_args
  val b = @{typ "'b"}
  val expected =
    mkh @{term_schem "\<not>C' \<Longrightarrow> (f :: ?'a \<Rightarrow> 'b) (?sk_w_args :: ?'a) = g ?sk_w_args \<Longrightarrow> \<not>D \<Longrightarrow> False"}
    |> HClause.map_hthm (Thm.instantiate' [SOME sk_with_args_typ] [SOME sk_with_args])
  val conclusion =
    Slam_Proof.reconstruct_neg_ext
      @{context}
      { premise = C, literal = 1, skolems = [(skolem_constant, skolem_constant_with_args, skolem_constant_definition)] }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

ML_val \<open>
  val C = mkh @{prop "\<not>C' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b) = (\<lambda>y. g y y) \<Longrightarrow> \<not>D \<Longrightarrow> False"}
  val expected =
    mk @{prop "\<not>C' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b) (SOME x. f x \<noteq> g x x) = g (SOME x. f x \<noteq> g x x) (SOME x. f x \<noteq> g x x) \<Longrightarrow> \<not>D \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_neg_ext
      @{context}
      { premise = C, literal = 1 }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

end