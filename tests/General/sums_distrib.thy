theory sums_distrib

imports JEHA.jeha HOL.Groups_Big HOL.Sledgehammer

begin

(*

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
  using sum.distrib [[jeha_trace, jeha_trace_forward_simp=false, jeha_trace_neg_cong_fun, jeha_debug_check_clauses]] by jeha
  (* sorry *)

lemma " (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j * g i j) + h i)
      = (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j) * (\<Prod>j\<in>B. g i j)) + (\<Sum>i\<in>A. h i)"
  by (metis (no_types, lifting) prod.cong prod.distrib sum.cong sum.distrib)
  (* by (metis (mono_tags, lifting) prod.cong prod.distrib sum.cong sum.distrib) *)
  (* This would easily work with NegCongFun. *)
  (* using prod.distrib sum.distrib [[jeha_trace, jeha_trace_forward_simp=false]] *)
  by jeha

*)

(*
lemma " P (\<Sum>i\<in>A. f i + h i + g i) (\<Prod>j\<in>B. f j * g j)
      = P ((\<Sum>i\<in>A. f i) + (\<Sum>i\<in>A. h i) + (\<Sum>i\<in>A. g i)) ((\<Prod>j\<in>B. f j) * (\<Prod>j\<in>B. g j))"
  by (metis (mono_tags, lifting) sum.cong sum.distrib prod.distrib)
*)

(*
lemma " (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j * g i j) + h i)
      = (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j) * (\<Prod>j\<in>B. g i j)) + (\<Sum>i\<in>A. h i)"
  (* using [[metis_trace]] *) by (metis (no_types, lifting) prod.cong prod.distrib sum.cong sum.distrib)
  (* 10 "clauses actually used" *)
*)

lemma " (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j * g i j) + h i)
      = (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j) * (\<Prod>j\<in>B. g i j)) + (\<Sum>i\<in>A. h i)"
  using [[jeha_trace]] by (jeha prod.distrib sum.distrib)

lemma "\<exists>h. (\<Sum>i\<in>A. f i + g i) = (\<Sum>i\<in>A. h i)"
  by metis
  (* using [[jeha_trace]] by jeha *)

(* find_theorems "(?x + ?y)^2" *)
thm Power.comm_semiring_1_class.power2_sum

lemma
  fixes "x" :: "'b ::{comm_ring_1}"
  shows
    "\<exists>c. (x\<^sup>2 + 2 * b * x) = (x + b)\<^sup>2 + c"
proof
  have "(x + b)\<^sup>2 = x\<^sup>2 + b\<^sup>2 + 2 * x * b" by (rule Power.comm_semiring_1_class.power2_sum)
  then show "(x\<^sup>2 + 2 * b * x) = (x + b)\<^sup>2 + (-b\<^sup>2)"
    by simp
qed
  
lemma
  fixes "x" :: "'b ::{comm_ring_1}"
  shows
    "\<exists>h. (x\<^sup>2 + 2 * b * x) = (x + b)\<^sup>2 + h b"
proof -
  (* have "(x + b)\<^sup>2 = x\<^sup>2 + b\<^sup>2 + 2 * x * b" by (rule Power.comm_semiring_1_class.power2_sum)
  then *) show ?thesis
    by (metis cancel_ab_semigroup_add_class.add_diff_cancel_left' group_add_class.add_minus_cancel)
qed

find_consts "nat \<Rightarrow> int"

find_theorems "finite ?A \<Longrightarrow> (\<Sum>x \<in> ?A. ?c) = Int.int (card A)"

thm Groups_Big.semiring_1_class.sum_constant

find_theorems "(\<Sum>x \<in> ?A. ?c * ?f x) = ?c * (\<Sum>x \<in> ?A. ?f x)"

thm sum.distrib

thm sum_distrib_left[symmetric]

find_theorems "?x = ?y \<Longrightarrow> ?z = ?u \<Longrightarrow> ?x + ?z = ?y + ?u"

lemma plus_right_cong:
  "x = y \<Longrightarrow> x + z = y + z"
  by simp

lemma plus_right_cancel:
  "(0 :: int) = y \<Longrightarrow> z = z + y"
  by presburger

thm arg_cong
thm fun_cong

lemma
  fixes "c" :: "int"
    and "A" :: "int set"
  shows
  "(\<Sum>x \<in> A. c * x) = c * (\<Sum>x \<in> A. x)"
  by (metis sum.cong sum_distrib_left)

thm allI

lemma assoc_and_comm: "(x :: int) + u + y + z = x + u + z + y"
  by presburger

find_theorems "?x + ?y + ?z = ?x + (?y + ?z)"

find_theorems "(?x :: int) = - ?y \<Longrightarrow> ?x + ?y = 0"

lemma eq_inv_imp_plus_eq_zero: "-(x :: int) = y \<Longrightarrow> x + y = 0"
  by simp

lemma
  fixes "b" :: int (* "'b ::{comm_ring_1}" *)
    and "A" :: "int set"
  assumes "finite I"
  shows
    "\<exists>h. \<forall>x. ((\<Sum>i\<in>I. (x i)\<^sup>2) + 2 * (\<Sum>i\<in>I. x i) * b) = (\<Sum>i\<in>I. (x i + b)\<^sup>2) + h I b"
  unfolding Power.comm_semiring_1_class.power2_sum
  unfolding sum.distrib
  unfolding sum_distrib_right[symmetric]
  unfolding sum_distrib_left[symmetric]
  unfolding Groups_Big.semiring_1_class.sum_constant
  apply (intro exI allI)
  apply (subst assoc_and_comm)
  apply (rule plus_right_cong)
  apply (subst Groups.semigroup_add_class.add.assoc)
  apply (rule plus_right_cancel)
  apply (simp)
  apply (rule eq_inv_imp_plus_eq_zero)
  apply simp
  done

(*
  thm plus_right_cong[of _ _ "2 * sum _ I * b"]
*)
  (* apply (rule plus_right_cong[of _ _ "2 * sum _ I * b"]) *)

  (* apply (rule fun_cong[of _ _ "\<lambda>x. 2 * sum x I * b"]) *)
  
  
(* proof (intro exI allI) *)
  

(* fact Groups.cancel_comm_monoid_add_class.diff_cancel) *)
  (* define h :: "int set \<Rightarrow> int \<Rightarrow> int" where "h = (\<lambda>A b. of_nat (card A) * b\<^sup>2)" *)
(*
  fix x
  (* show "(\<Sum>i\<in>I. (x i)\<^sup>2) + 2 * (\<Sum>i\<in> I. x i) * b = (\<Sum>i\<in>I. ((x i) + b)\<^sup>2) + (- of_nat (card I) * b\<^sup>2)" *)

  show "(\<Sum>i\<in>I. (x i)\<^sup>2) + 2 * sum x I * b = (\<Sum>i\<in>I. (x i)\<^sup>2) + int (card I) * b\<^sup>2 + 2 * sum x I * b + (- of_nat (card I) * b\<^sup>2)"
    by simp
*)
  

  (* sledgehammer(Groups_Big.semiring_1_class.sum_constant) *)
  (* by (jeha add_minus_cancel) *)
  (* by (jeha add_minus_cancel mult.commute mult_2 sum_distrib_left sum_distrib_right uminus_add_conv_diff) *)

find_theorems "?x + ?y + ?z = ?x + (?y + ?z)"
find_theorems "?x - ?x = 0"

lemma
  fixes "b" :: int (* "'b ::{comm_ring_1}" *)
    and "A" :: "int set"
  assumes "finite I"
  shows
    "\<exists>h. \<forall>x. ((\<Sum>i\<in>I. (x i)\<^sup>2) + 2 * (\<Sum>i\<in>I. x i) * b) = (\<Sum>i\<in>I. (x i + b)\<^sup>2) + h I b"
  using assms Power.comm_semiring_1_class.power2_sum sum.distrib sum_distrib_right sum_distrib_left Groups_Big.semiring_1_class.sum_constant Groups.cancel_comm_monoid_add_class.diff_cancel assoc_and_comm plus_right_cong Groups.semigroup_add_class.add.assoc plus_right_cancel eq_inv_imp_plus_eq_zero
  (* using [[jeha_trace, jeha_trace_forward_simp=false, jeha_max_number_of_steps=3000]] by jeha *)
  sorry

  (* using [[jeha_trace, jeha_trace_forward_simp=false, jeha_max_number_of_steps=300]] by (jeha Power.comm_semiring_1_class.power2_sum sum.distrib sum_distrib_right sum_distrib_left Groups_Big.semiring_1_class.sum_constant Groups.cancel_comm_monoid_add_class.diff_cancel assoc_and_comm plus_right_cong Groups.semigroup_add_class.add.assoc plus_right_cancel eq_inv_imp_plus_eq_zero) *)

lemma plus_right_remove:
  "x = y \<Longrightarrow> (x :: int) + z = y + z"
  by auto

lemma
  fixes "b" :: int (* "'b ::{comm_ring_1}" *)
    and "A" :: "int set"
  assumes "finite I"
  shows
    "\<exists>h. \<forall>x. (h I b + (\<Sum>i\<in>I. (x i)\<^sup>2) + 2 * b * (\<Sum>i\<in>I. x i)) = (\<Sum>i\<in>I. (b + x i)\<^sup>2)"
  apply (intro exI allI)
  unfolding power2_sum
  unfolding sum.distrib
  unfolding sum_distrib_left
  apply (rule plus_right_remove)
  apply (rule plus_right_remove)
  apply (simp)
  done
(*
  using assms Power.comm_semiring_1_class.power2_sum sum.distrib sum_distrib_right sum_distrib_left Groups_Big.semiring_1_class.sum_constant Groups.cancel_comm_monoid_add_class.diff_cancel assoc_and_comm plus_right_cong Groups.semigroup_add_class.add.assoc plus_right_cancel eq_inv_imp_plus_eq_zero
*)

lemma
  fixes "b" :: int (* "'b ::{comm_ring_1}" *)
    and "A" :: "int set"
  assumes "finite I"
  shows
    "\<exists>h. \<forall>x. (h I b + (\<Sum>i\<in>I. (x i)\<^sup>2) + 2 * b * (\<Sum>i\<in>I. x i)) = (\<Sum>i\<in>I. (b + x i)\<^sup>2)"
  apply (intro exI allI)
  sledgehammer[vampire] (power2_sum sum.distrib sum_distrib_left plus_right_remove)
  (* using assms [[jeha_trace, jeha_trace_forward_simp=false]] by (jeha power2_sum sum.distrib sum_distrib_left plus_right_remove) *)

lemma
  fixes "b" :: int (* "'b ::{comm_ring_1}" *)
  shows
    "\<exists>h. \<forall>x. x\<^sup>2 + 2 * x * b = (x + b)\<^sup>2 + h b"
proof (intro exI allI)
  fix x
  show "x\<^sup>2 + 2 * x * b = (x + b)\<^sup>2 + (- b\<^sup>2)"
    unfolding Power.comm_semiring_1_class.power2_sum
    by simp
qed

lemma
  fixes "b" :: int (* "'b ::{comm_ring_1}" *)
  shows
    "\<exists>h. \<forall>x. x\<^sup>2 + h b + 2 * x * b = (x + b)\<^sup>2"
proof (intro exI allI)
  fix x
  show "x\<^sup>2 + b\<^sup>2 + 2 * x * b = (x + b)\<^sup>2"
    (* by (metis power2_sum) *)
    by (jeha power2_sum)
qed
    (* sledgehammer[zipperposition, dont_try0] (Power.comm_semiring_1_class.power2_sum) *)
(*
    using [[jeha_trace, jeha_trace_forward_simp=false, (* jeha_trace_sup, *) jeha_max_number_of_steps=300]] by (jeha Power.comm_semiring_1_class.power2_sum add.commute  Groups.semigroup_add_class.add.assoc) (*   add.left_commute add_minus_cancel) *)
*)

lemma
  fixes "b" :: int (* "'b ::{comm_ring_1}" *)
  shows
    "\<exists>h. \<forall>x. x\<^sup>2 + h b + 2 * x * b = (x + b)\<^sup>2"
  by (metis add_diff_cancel_left' power2_sum)

(* by (jeha Power.comm_semiring_1_class.power2_sum sum.distrib sum_distrib_right sum_distrib_left Groups_Big.semiring_1_class.sum_constant) *)

(*
lemma " (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j * g i j))
      = (\<Sum>i\<in>A. (\<Prod>j\<in>B. f i j) * (\<Prod>j\<in>B. g i j))"
  by (jeha prod.distrib)
*)

(*

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

*)

end