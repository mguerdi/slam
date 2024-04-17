theory misc

imports "JEHA_TEST_BASE.test_base"

begin

declare [[jeha_trace]]
declare [[metis_trace]]

declare [[jeha_proof_reconstruction]]

lemma funs_eq_then_comp_id_eq:
  shows "f = g \<Longrightarrow> (\<And> x. f x = (id o g) x)"
  (* by (metis fun.map_id) *)
  using
    [[ jeha_disable_all,
        jeha_rule_sup,
        jeha_rule_arg_cong,
        jeha_rule_clause_subsumption,
        jeha_rule_e_res,
        unify_search_bound = 7 ]]
  by (jeha comp_apply id_apply) (* 1070 ms *)

lemma arg_cong_test:
  shows "g = f \<Longrightarrow> g a = f a"
  (* by metis *)
  using [[jeha_disable_all, jeha_rule_arg_cong, jeha_rule_sup, jeha_rule_e_res]]
  by jeha

lemma funext_test:
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
  by (jeha ext) (* 1000 ms *)

lemma ap_eq_test:
  shows "g = f \<Longrightarrow> (\<And> x. f x = g x)"
  (* by metis *)
  using
    [[ jeha_disable_all,
        jeha_rule_arg_cong,
        jeha_rule_sup,
        jeha_rule_e_res ]]
  by jeha (* 45 ms *)

lemma ap_fa_eq_test:
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
        jeha_proof_reconstruction = false,
        metis_trace ]]
  by jeha (* 455 ms *)

lemma
  shows "(1 :: nat) + 1 = 2"
  by (jeha (dump) Num.nat_1_add_1) (* 51 ms *)

(* b \<approx> a, (\<lambda>x. b) !\<approx> (\<lambda> x. a) *)
lemma
  shows "a = b \<Longrightarrow> (\<lambda>x. b) = (\<lambda>x .a)"
  (* by metis *)
  (* lost in unification: *)
  (* using [[ jeha_trace ]] by (jeha ext) *)
  oops

lemma
  shows "(\<lambda> x. b) = (\<lambda> x. a) \<Longrightarrow> a = b"
  (* by metis *)
  by jeha (* 44 ms *)

lemma
  shows "g = f \<Longrightarrow> f a b c = d \<Longrightarrow> \<forall> h. h a \<noteq> d \<Longrightarrow> False"
  (* by (metis fun_upd_apply) (* vampire *) *)
  (* FIXME: activate proof reconstruction once NS reuses the substitution *)
  using [[ jeha_proof_reconstruction = false ]] by jeha (* 132 ms *)

lemma
  shows "\<forall> x y. g x y = f y x \<Longrightarrow> g c \<noteq> (\<lambda> y. f y c) \<Longrightarrow> False"
  by (jeha ext) (* 223 ms *)

end