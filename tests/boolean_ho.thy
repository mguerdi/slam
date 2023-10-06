theory boolean_ho

imports "test_base"

begin

ML_val \<open>
  val c = JClause.of_term (@{term_pat "(\<forall> x. ?y x = (p x \<and> q x)) = False"}, 0)
  val subterm = JClause.subterm_at_full_pos c ([], JLit.Left, 0)
  val c' = Jeha.infer_forall_rw @{context} c ([], JLit.Left, 0)
\<close>

declare [[jeha_trace = true]]

ML \<open>
  val sb = Config.get @{context} Unify.search_bound
  val tb = Config.get @{context} Unify.trace_bound
\<close>

declare [[unify_search_bound = 10]]
declare [[unify_trace_bound = 10]]

ML \<open>
  val sb = Config.get @{context} Unify.search_bound
  val tb = Config.get @{context} Unify.trace_bound
\<close>

(* declare [[ jeha_disable_all ]] *)
declare [[ jeha_rule_forall_rw ]]

ML_val \<open>
  val c = JClause.of_term (@{term_pat "(\<forall> x. ?y x = (p x \<and> q x)) = False"}, 0)
  val subterm = JClause.subterm_at_full_pos c ([], JLit.Left, 0)
  val c' = Jeha.infer_forall_rw @{context} c ([], JLit.Left, 0)
\<close>

ML_val \<open>
  val all_disabled = Config.get @{context} Jeha_Common.disable_all
  val sup_enabeld = Config.get @{context} Jeha_Common.rule_sup
\<close>

lemma fa_rw_test:
  shows "\<And>y. (\<forall> x. y x = (p x \<and> q x))"
  (* ML_val \<open>
    val g = @{Isar.goal}
    val atomized_ths = map (Conv.fconv_rule (Object_Logic.atomize @{context})) [#goal g]
  \<close> *)
  by (jeha)

end