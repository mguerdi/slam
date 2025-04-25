theory subsumption

imports JEHA_TEST_BASE.test_base

begin

declare [[jeha_trace]]
declare [[jeha_disable_all]]
declare [[jeha_rule_clause_subsumption]]
declare [[jeha_trace_forward_simp]]
declare [[jeha_trace_backward_simp]]
declare [[jeha_trace_simp_steps]]

ML \<open>
  val c = JClause.of_term @{context} (@{term "a \<or> b"}, 0)
  val d = JClause.of_term @{context} (@{term_schem "?x \<or> b"}, 1)
  val () = writeln (Jeha_Common.pretty_terms @{context} (map JClause.term_of [c, d]))
  val symbols = Subsumption_Index.collect_symbols [c, d] 
  val index =
    Subsumption_Index.make_index symbols
    |> Subsumption_Index.insert_clause d
  val () = \<^assert> ([1] = Subsumption_Index.fold_subsuming c (curry op::) index [])
\<close>

ML \<open>
  val c = JClause.of_term @{context} (@{term "a \<or> b"}, 0)
  val d = JClause.of_term @{context} (@{term_schem "?x \<or> b"}, 1)
  val () = writeln (Jeha_Common.pretty_terms @{context} (map JClause.term_of [c, d]))
  val symbols = Subsumption_Index.collect_symbols [c, d] 
  val index =
    Subsumption_Index.make_index symbols
    |> Subsumption_Index.insert_clause c
  val () = \<^assert> ([] = Subsumption_Index.fold_subsuming d (curry op::) index [])
\<close>

lemma "(\<And>x. f x) \<Longrightarrow> f a \<or> False \<Longrightarrow> f b"
  using [[jeha_rule_forall_hoist, jeha_rule_simp_false_elim]] by jeha

end
