theory simp_bool_rw

imports "test_base"

begin

declare [[jeha_trace]]
declare [[jeha_trace_cheap_simplify]]

declare [[jeha_disable_all]]

declare [[jeha_rule_simp_false_elim]]
declare [[jeha_rule_simp_bool_rw]]
declare [[jeha_rule_simp_outer_claus]]

ML_val \<open>
  val neg_conj = JClause.of_term (@{term "a \<noteq> b"}, 1);
  val assum = JClause.of_term (@{term "(\<forall>z. z a = True \<longrightarrow> z b = True) = True"}, 2);
  (* this is what was inferred *)
  val c = JClause.of_term (@{term_schem "?x a = True \<longrightarrow> ?x b = True"}, 3);
  (* this is the result of cheap simplification *)
  val wrong = @{term "False = False"};
  (* cheap simplify *)
  val simplified = Jeha.forward_simplify @{context} false [neg_conj, assum] c
\<close>

end