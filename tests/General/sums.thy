theory sums 

imports JEHA.jeha HOL.Main

begin

lemma " (\<Sum>i\<in>A. i\<^sup>2  +         i * 2  +          1)
      = (\<Sum>i\<in>A. i\<^sup>2) + (\<Sum>i\<in>A. i * 2) + (\<Sum>i\<in>A. 1)"
  (* sledgehammer [dont_try0] *)
  (* using [[metis_trace]] by (metis sum.distrib) (* times out >1s *) *)
  using [[jeha_trace, jeha_proof_reconstruction=argo, metis_trace]] by (jeha sum.distrib) (* 84 ms *)

thm sum.distrib

(* without simplifications *)
lemma "(\<Sum>i\<in>A. i\<^sup>2 + i * 2 + 1) = (\<Sum>i\<in>A. i\<^sup>2) + (\<Sum>i\<in>A. i * 2) + (\<Sum>i\<in>A. 1)"
  (* sledgehammer [dont_try0]
  by (metis sum.distrib) (* times out >1s *) *)
  using [[
          jeha_disable_all
        , jeha_rule_sup
        , jeha_rule_e_res
        , jeha_rule_e_fact
        , jeha_rule_clause_subsumption
        , jeha_max_number_of_steps = 200
        , jeha_report_main_loop_timing
        (* , jeha_trace *)
        , jeha_proof_reconstruction=argo
        ]]
  using sum.distrib by jeha (* 8000 ms *)

end
