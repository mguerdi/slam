theory lem_issue 

imports SLAM_TEST_BASE.test_base "HOL.Set" "HOL.Sledgehammer"

begin

(* From SuperCalc/superposition.thy *)

lemma
  assumes "x \<in> (A \<union> B)"
  shows "x \<in> A \<or> x \<in> B"
  using assms by (slam UnE) (* fixed by e9e509e *)

declare [[slam_trace, slam_trace_sup]]

(* Problematic inferences of LEM with itself: *)
ML\<open>
  val C = JClause.of_term @{context} (@{term_schem "?P = True \<or> ?P = False"}, 0)
  val D = JClause.of_term @{context} (@{term_schem "?Q = True \<or> ?Q = False"}, 0)
  val concl =
    Slam.infer_sup
      @{context}
      (C, (JLit.Right, 1), JClause.PotentiallyMaximal)
      (D, ([], JLit.Right, 1), JClause.PotentiallyMaximal)
\<close>

end