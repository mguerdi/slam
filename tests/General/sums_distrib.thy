theory sums_distrib

imports JEHA.jeha HOL.Groups_Big

begin

lemma sums_distrib:
  " (\<Sum>i\<in>A. i\<^sup>2  +         i * 2  +          1)
  = (\<Sum>i\<in>A. i\<^sup>2) + (\<Sum>i\<in>A. i * 2) + (\<Sum>i\<in>A. 1)"
  (* sledgehammer suggests
  - zipperposition: Try this: by (simp add: sum.distrib) (12 ms) *)
  (* sledgehammer[dont_try0] suggests
  - zipperposition: Try this: by (metis (lifting) ext sum.distrib) (1.2 s) 
  - vampire: Try this: by (metis (mono_tags, lifting) sum.cong sum.distrib) (327 ms) 
  - cvc4: Try this: by (smt (verit) sum.cong sum.distrib) (176 ms) *)
  using sum.distrib by jeha (* 21 ms *)

(* without simplifications *)
lemma sums_distrib_restricted:
  " (\<Sum>i\<in>A. i\<^sup>2  +         i * 2  +          1)
  = (\<Sum>i\<in>A. i\<^sup>2) + (\<Sum>i\<in>A. i * 2) + (\<Sum>i\<in>A. 1)"
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
        ]]
  using sum.distrib by jeha (* 9 ms *)

lemma "(\<Sum>i\<in>A. (\<Sum>j\<in>A. f i j + g i j)) = (\<Sum>i\<in>A. \<Sum>j\<in>A. f i j) + (\<Sum>i\<in>A. \<Sum>j\<in>A. g i j)"
  (* by (metis (mono_tags, lifting) sum.cong sum.distrib) *)

  (* This would easily work with NegCongFun. *)
  (* But: How would it ever work without? FluidSup? Ext? *)
  (* using sum.distrib by jeha *)
  sorry

lemma " (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j * g i j) + h i)
      = (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j) * (\<Prod>j\<in>B. g i j)) + (\<Sum>i\<in>A. h i)"
  (* by (metis (mono_tags, lifting) prod.cong prod.distrib sum.cong sum.distrib) *)
  (* This would easily work with NegCongFun. *)
  (* using prod.distrib sum.distrib [[jeha_trace, jeha_trace_forward_simp=false]] by jeha *)
  sorry

lemma " P (\<Sum>i\<in>A. f i + h i + g i) (\<Prod>j\<in>B. f j * g j)
      = P ((\<Sum>i\<in>A. f i) + (\<Sum>i\<in>A. h i) + (\<Sum>i\<in>A. g i)) ((\<Prod>j\<in>B. f j) * (\<Prod>j\<in>B. g j))"
  (* by (jeha sum.distrib prod.distrib) *)
  by (metis (mono_tags, lifting) sum.cong sum.distrib prod.distrib)

lemma "((x :: nat) + y)\<^sup>2 = x\<^sup>2 + 2 * x * y + y\<^sup>2"
  by (simp add: power2_sum)

lemma
  fixes A :: "nat set"
  shows
    " (\<Sum>i\<in>A. (i + 1)\<^sup>2)
    = (\<Sum>i\<in>A. i\<^sup>2 + i * 2) + (\<Sum>i\<in>A. 1)"
  (* unfolding power2_sum (*  sledgehammer *) *) 
  unfolding power2_sum one_power2 mult.comm_neutral
  (* using [[jeha_trace]] by (jeha sum.distrib) *)
  (* sledgehammer *)
  (* by (metis Suc_1 ab_semigroup_add_class.add_ac(1) add.commute mult.commute sum.distrib) *)
  (* by (jeha Suc_1 ab_semigroup_add_class.add_ac(1) add.commute mult.commute sum.distrib) *)
  unfolding add.assoc[of "_" 1 "_"]
  unfolding add.commute[of 1 "2 * _"]
  unfolding add.assoc[of "_" "2 * _" "_", symmetric]
  (* unfolding mult.commute[of "2" "_"] *)
  (*
  using [[jeha_trace, jeha_trace_forward_simp=false, jeha_max_number_of_steps=1000, jeha_unify_timeout_ms=5]]
    by (jeha sum.distrib mult.commute[of "2"])
  *)
  sorry

end