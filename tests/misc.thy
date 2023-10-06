theory misc

imports "test_base"

begin

declare [[jeha_trace]]

declare [[jeha_proof_reconstruction]]

lemma funs_eq_then_comp_id_eq:
  shows "f = g \<Longrightarrow> (\<And> x. f x = (id o g) x)"
  using
    [[ jeha_disable_all,
        jeha_rule_sup,
        jeha_rule_arg_cong,
        jeha_rule_clause_subsumption,
        jeha_rule_e_res,
        unify_search_bound = 7 ]]
  by (jeha comp_apply id_apply)

lemma arg_cong_test:
  shows "g = f \<Longrightarrow> g a = f a"
  using [[jeha_disable_all, jeha_rule_arg_cong, jeha_rule_sup, jeha_rule_e_res]]
  by jeha

lemma funext_test:
  shows "\<forall> x . g x = f x \<Longrightarrow> f = g"
  using
    [[ jeha_disable_all,
        jeha_rule_forall_rw,
        jeha_rule_sup,
        jeha_rule_bool_rw,
        jeha_rule_clause_subsumption,
        jeha_rule_eq_hoist,
        jeha_rule_false_elim ]]
  by (jeha ext)

lemma ap_eq_test:
  shows "g = f \<Longrightarrow> (\<And> x. f x = g x)"
  using
    [[ jeha_disable_all,
        jeha_rule_arg_cong,
        jeha_rule_sup,
        jeha_rule_e_res ]]
  by jeha

lemma ap_fa_eq_test:
  shows "g = f \<Longrightarrow> \<forall>x . f x = g x"
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
  by jeha

lemma
  shows "(1 :: nat) + 1 = 2"
  by (jeha (dump) Num.nat_1_add_1)

end