theory misc

imports "JEHA_TEST_BASE.test_base" HOL.Num

begin

notation (output) "Pure.prop" ("#_" [1000] 1000)

lemma funs_eq_then_comp_id_eq:
  shows "f = g \<Longrightarrow> (\<And> x. f x = (id o g) x)"
  (* by (metis fun.map_id) *)
  using comp_apply id_apply
  by jeha (* 94 ms *)

lemma funs_eq_then_comp_id_eq_restricted:
  shows "f = g \<Longrightarrow> (\<And> x. f x = (id o g) x)"
  (* by (metis fun.map_id) *)
  using comp_apply id_apply
    [[  jeha_disable_all,
        jeha_rule_sup,
        jeha_rule_arg_cong,
        jeha_rule_clause_subsumption,
        jeha_rule_e_res,
        jeha_rule_rewrite_negative_lits,
        jeha_rule_rewrite_positive_lits
        ]]
  by jeha (* 53 ms *)

lemma arg_cong_test:
  shows "g = f \<Longrightarrow> g a = f a"
  (* by metis *)
  using [[jeha_disable_all, jeha_rule_arg_cong, jeha_rule_sup, jeha_rule_e_res]]
  by jeha (* 2 ms *)

lemma arg_cong_multiple_vars_test:
  shows "g = f \<Longrightarrow> g a b c = f a b c"
  using [[jeha_disable_all, jeha_rule_arg_cong, jeha_rule_sup, jeha_rule_e_res]]
  by jeha (* 13 ms *)

lemma funext_test:
  shows "\<forall> x . g x = f x \<Longrightarrow> f = g"
  (* by (metis ext) *)
  by jeha (* 3 ms *)

lemma funext_test_restricted:
  shows "\<forall> x . g x = f x \<Longrightarrow> f = g"
  (* by (metis ext) *)
  using
    [[ jeha_disable_all,
        jeha_rule_forall_rw,
        jeha_rule_sup,
        jeha_rule_bool_rw,
        jeha_rule_clause_subsumption,
        jeha_rule_eq_hoist,
        jeha_rule_false_elim,
        jeha_rule_e_res ]]
  using ext by jeha (* 28 ms *)

lemma ap_eq_test:
  shows "g = f \<Longrightarrow> (\<And> x. f x = g x)"
  (* by metis *)
  using
    [[ jeha_disable_all,
        jeha_rule_arg_cong,
        jeha_rule_sup,
        jeha_rule_e_res ]]
  by jeha (* 1 ms *)

lemma ap_fa_eq_test:
  shows "g = f \<Longrightarrow> \<forall>x . f x = g x"
  by jeha (* 11 ms *)

lemma ap_fa_eq_test_restricted:
  shows "g = f \<Longrightarrow> \<forall>x . f x = g x"
  (* by metis *)
  using
    [[ jeha_disable_all,
        jeha_rule_sup,
        jeha_rule_forall_rw,
        jeha_rule_arg_cong,
        jeha_rule_bool_rw,
        jeha_rule_eq_hoist,
        jeha_rule_bool_hoist,
        jeha_rule_false_elim,
        metis_trace ]]
  by jeha (* 16 ms *)

lemma
  shows "(1 :: nat) + 1 = 2"
  using Num.nat_1_add_1 by jeha (* 3 ms *)

(* b \<approx> a, (\<lambda>x. b) !\<approx> (\<lambda> x. a) *)
lemma eq_implies_const_abstraction_eq:
  shows "a = b \<Longrightarrow> (\<lambda>x. b) = (\<lambda>x .a)"
  (* by metis *)
  using ext by jeha (* 6 ms *)

lemma eq_implies_const_abstraction_eq_neg_ext:
  shows "a = b \<Longrightarrow> (\<lambda>x. b) = (\<lambda>x .a)"
  by jeha (* 3 ms *)

lemma
  shows "(\<lambda> x. b) = (\<lambda> x. a) \<Longrightarrow> a = b"
  by jeha (* 3 ms *)

lemma
  shows "g = f \<Longrightarrow> f a b c = d \<Longrightarrow> \<forall> h. h a \<noteq> d \<Longrightarrow> False"
  (* by (metis fun_upd_apply) (* vampire *) *)
  by jeha (* 11 ms *)

lemma
  shows "\<forall> x y. g x y = f y x \<Longrightarrow> g c \<noteq> (\<lambda> y. f y c) \<Longrightarrow> False"
  by jeha (* 7 ms *)

lemma
  shows "\<forall> x y. g x y = f y x \<Longrightarrow> g c \<noteq> (\<lambda> y. f y c) \<Longrightarrow> False"
  using ext by jeha (* 16 ms *)

end