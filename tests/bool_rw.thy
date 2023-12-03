theory bool_rw

imports "test_base"

begin

ML_val \<open>
  (* val c = JClause.of_term (@{term_schem "(True \<longrightarrow> False) = d"}, 0); *)
  val c = JClause.of_term (@{term "(True \<longrightarrow> True = True) = True \<or> False = True"}, 0);
  val fp = ([2], JLit.Left, 0);
  val t = JClause.subterm_at_full_pos c fp;
  val rws = Jeha.simp_bool_rw @{context} c fp;
  val _ = writeln (JClause.pretty_clauses @{context} rws)
  val them = Jeha.bool_rw_non_var_rules;
\<close>

end