theory misc

imports "SLAM_TEST_BASE.test_base" HOL.Num

begin

notation (output) "Pure.prop" ("#_" [1000] 1000)

lemma funs_eq_then_comp_id_eq:
  shows "f = g \<Longrightarrow> (\<And> x. f x = (id o g) x)"
  (* by (metis fun.map_id) *)
  using comp_apply id_apply
  by slam (* 94 ms *)

lemma funs_eq_then_comp_id_eq_restricted:
  shows "f = g \<Longrightarrow> (\<And> x. f x = (id o g) x)"
  (* by (metis fun.map_id) *)
  using comp_apply id_apply
    [[  slam_disable_all,
        slam_rule_sup,
        slam_rule_arg_cong,
        slam_rule_clause_subsumption,
        slam_rule_e_res,
        slam_rule_rewrite_negative_lits,
        slam_rule_rewrite_positive_lits
        ]]
  by slam (* 53 ms *)

lemma arg_cong_test:
  shows "g = f \<Longrightarrow> g a = f a"
  (* by metis *)
  using [[slam_disable_all, slam_rule_arg_cong, slam_rule_sup, slam_rule_e_res]]
  by slam (* 2 ms *)

lemma arg_cong_multiple_vars_test:
  shows "g = f \<Longrightarrow> g a b c = f a b c"
  using [[slam_disable_all, slam_rule_arg_cong, slam_rule_sup, slam_rule_e_res]]
  by slam (* 13 ms *)

lemma funext_test:
  shows "\<forall> x . g x = f x \<Longrightarrow> f = g"
  (* by (metis ext) *)
  by slam (* 3 ms *)

lemma funext_test_restricted:
  shows "\<forall> x . g x = f x \<Longrightarrow> f = g"
  (* by (metis ext) *)
  using
    [[ slam_disable_all,
        slam_rule_forall_rw,
        slam_rule_sup,
        slam_rule_bool_rw,
        slam_rule_clause_subsumption,
        slam_rule_eq_hoist,
        slam_rule_false_elim,
        slam_rule_e_res ]]
  using ext by slam (* 28 ms *)

lemma ap_eq_test:
  shows "g = f \<Longrightarrow> (\<And> x. f x = g x)"
  (* by metis *)
  using
    [[ slam_disable_all,
        slam_rule_arg_cong,
        slam_rule_sup,
        slam_rule_e_res ]]
  by slam (* 1 ms *)

lemma ap_fa_eq_test:
  shows "g = f \<Longrightarrow> \<forall>x . f x = g x"
  by slam (* 11 ms *)

lemma ap_fa_eq_test_restricted:
  shows "g = f \<Longrightarrow> \<forall>x . f x = g x"
  (* by metis *)
  using
    [[ slam_disable_all,
        slam_rule_sup,
        slam_rule_forall_rw,
        slam_rule_arg_cong,
        slam_rule_bool_rw,
        slam_rule_eq_hoist,
        slam_rule_bool_hoist,
        slam_rule_false_elim,
        metis_trace ]]
  by slam (* 16 ms *)

lemma
  shows "(1 :: nat) + 1 = 2"
  using Num.nat_1_add_1 by slam (* 3 ms *)

(* b \<approx> a, (\<lambda>x. b) !\<approx> (\<lambda> x. a) *)
lemma eq_implies_const_abstraction_eq:
  shows "a = b \<Longrightarrow> (\<lambda>x. b) = (\<lambda>x .a)"
  (* by metis *)
  using ext by slam (* 6 ms *)

lemma eq_implies_const_abstraction_eq_neg_ext:
  shows "a = b \<Longrightarrow> (\<lambda>x. b) = (\<lambda>x .a)"
  by slam (* 3 ms *)

lemma
  shows "(\<lambda> x. b) = (\<lambda> x. a) \<Longrightarrow> a = b"
  by slam (* 3 ms *)

lemma
  shows "g = f \<Longrightarrow> f a b c = d \<Longrightarrow> \<forall> h. h a \<noteq> d \<Longrightarrow> False"
  (* by (metis fun_upd_apply) (* vampire *) *)
  by slam (* 11 ms *)

lemma
  shows "\<forall> x y. g x y = f y x \<Longrightarrow> g c \<noteq> (\<lambda> y. f y c) \<Longrightarrow> False"
  by slam (* 7 ms *)

lemma
  shows "\<forall> x y. g x y = f y x \<Longrightarrow> g c \<noteq> (\<lambda> y. f y c) \<Longrightarrow> False"
  using ext by slam (* 16 ms *)

end