theory sums_distrib

imports SLAM.slam HOL.Groups_Big HOL.Sledgehammer

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
  using sum.distrib by slam (* 21 ms *)

(* without simplifications *)
lemma sums_distrib_restricted:
  " (\<Sum>i\<in>A. i\<^sup>2  +         i * 2  +          1)
  = (\<Sum>i\<in>A. i\<^sup>2) + (\<Sum>i\<in>A. i * 2) + (\<Sum>i\<in>A. 1)"
  (* sledgehammer [dont_try0]
  by (metis sum.distrib) (* times out >1s *) *)
  using [[
          slam_disable_all
        , slam_rule_sup
        , slam_rule_e_res
        , slam_rule_e_fact
        , slam_rule_clause_subsumption
        , slam_max_number_of_steps = 200
        , slam_report_main_loop_timing
        ]]
  using sum.distrib by slam (* 9 ms *)

lemma "(\<Sum>i\<in>A. (\<Sum>j\<in>A. f i j + g i j)) = (\<Sum>i\<in>A. \<Sum>j\<in>A. f i j) + (\<Sum>i\<in>A. \<Sum>j\<in>A. g i j)"
  (* by (metis (mono_tags, lifting) sum.cong sum.distrib) *)
  using sum.distrib [[slam_trace, slam_trace_forward_simp=false]] by slam

lemma " (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j * g i j) + h i)
      = (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j) * (\<Prod>j\<in>B. g i j)) + (\<Sum>i\<in>A. h i)"
  (* by (metis (no_types, lifting) prod.cong prod.distrib sum.cong sum.distrib) *)
  (* by (metis (mono_tags, lifting) prod.cong prod.distrib sum.cong sum.distrib) *)
  using prod.distrib sum.distrib [[slam_trace, slam_trace_forward_simp=false]] by slam

lemma " P (\<Sum>i\<in>A. f i + h i + g i) (\<Prod>j\<in>B. f j * g j)
      = P ((\<Sum>i\<in>A. f i) + (\<Sum>i\<in>A. h i) + (\<Sum>i\<in>A. g i)) ((\<Prod>j\<in>B. f j) * (\<Prod>j\<in>B. g j))"
  (* by (metis (mono_tags, lifting) sum.cong sum.distrib prod.distrib) *)
  by (slam (mono_tags, lifting) sum.cong sum.distrib prod.distrib)

lemma " (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j * g i j) + h i)
      = (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j) * (\<Prod>j\<in>B. g i j)) + (\<Sum>i\<in>A. h i)"
  (* 10 "clauses actually used" *)
  (* by (metis (no_types, lifting) prod.cong prod.distrib sum.cong sum.distrib) *)
  by (slam (no_types, lifting) prod.cong prod.distrib sum.cong sum.distrib)

lemma " (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j * g i j) + h i)
      = (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j) * (\<Prod>j\<in>B. g i j)) + (\<Sum>i\<in>A. h i)"
  using [[slam_trace]] by (slam prod.distrib sum.distrib)

lemma "\<exists>h. (\<Sum>i\<in>A. f i + g i) = (\<Sum>i\<in>A. h i)"
  (* by metis *)
  using [[slam_trace, slam_trace_forward_simp=false]] by slam

lemma " (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j * g i j))
      = (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j) * (\<Prod>j\<in>B. g i j))"
  (* by (metis prod.distrib) *)
  by (slam prod.distrib)

lemma "((x :: nat) + y)\<^sup>2 = x\<^sup>2 + 2 * x * y + y\<^sup>2"
  by (simp add: power2_sum)

lemma
  fixes A :: "nat set"
  shows "(\<Sum>i\<in>A. i\<^sup>2 + 1 + 2 * i) = (\<Sum>i\<in>A. i\<^sup>2 + i * 2) + (\<Sum>i\<in>A. 1)"
  (* using [[slam_trace, slam_trace_forward_simp=false]] *)
  (* by (slam Suc_1 ab_semigroup_add_class.add_ac(1) add.commute mult.commute sum.distrib) *)

  (* sledgehammer suggests the following: *)

  (* (the times are from the timing panel) *)

  (* by (smt (z3) add.commute add.left_commute mult_2 mult_2_right sum.cong sum.distrib) (* 199 ms *) *)

  (* by (metis (no_types, lifting) Suc_eq_plus1 add_Suc mult.commute sum.cong sum.distrib) (* 236 ms *) *)

  (* fastest: *)
  by (slam (no_types, lifting) Suc_eq_plus1 add_Suc mult.commute sum.cong sum.distrib) (* 120 ms *)

  (* by (metis add.assoc add.commute mult_2 mult_2_right sum.distrib) *) (* very long *)
  (* by (slam add.assoc add.commute mult_2 mult_2_right sum.distrib) (* very long *) *)

  (* instantiated: *)
  (* by (metis (lifting) ext add.assoc[of "_ ^ 2"] add.assoc[of "1" "_ ^ 2" "2 * _"] add.commute[of "1" "_ ^ 2 + _ + _"] add.commute[of "1" "_ ^ 2"] mult_2
      mult_2_right sum.distrib[of "\<lambda>uu. uu\<^sup>2 + uu * 2" "\<lambda>uu. 1" A]) (* 50 ms *) *)

  (* by (metis (no_types, lifting) Suc_eq_plus1 add_Suc mult.commute sum.cong sum.distrib) *)
  (* by (slam add.assoc add.commute mult_2 mult_2_right sum.distrib) *)

end