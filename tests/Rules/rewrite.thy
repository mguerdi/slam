theory rewrite

imports SLAM_TEST_BASE.test_base

begin

declare [[show_types]]
declare [[slam_trace, slam_trace_sup]]

ML \<open>
  val c = JClause.of_term @{context} (@{term_schem "id (?f :: ?'a \<Rightarrow> ?'b) ?x = ?f ?x"}, 0)
  val d = JClause.of_term @{context} (@{term_schem "?y = id (\<lambda>a. id ?y) ?z"}, 1)
  (* This rewrite fails because the ?y inside of the lambda is fresh. *)
  val ctxt = Config.put Slam_Common.trace_rewrite_positive_lits true @{context}
  val d' = Slam.simp_rewrite_positive_lits ctxt (c, JLit.Left) (d, ([], JLit.Right, 0))
\<close>

end