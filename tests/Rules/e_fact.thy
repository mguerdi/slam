theory e_fact

imports SLAM_TEST_BASE.test_base 

begin

ML_val \<open>
  val ctxt =
    @{context} 
    |> Config.put Slam_Common.trace_e_fact true
    |> Config.put Slam_Common.trace true
  val c = JClause.of_term ctxt (@{term "True = False \<or> True = False"}, 0);
  val ds = Slam.infer_efact ctxt c ((JLit.Left, 0), (JLit.Left, 1))
\<close>

end