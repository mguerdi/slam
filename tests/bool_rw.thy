theory bool_rw

imports "test_base"

begin

ML_val \<open>
  val c = JClause.of_term (@{term "(True \<longrightarrow> True = True) = True \<or> False = True"}, 0);
  val true_eq_true_position = ([2], JLit.Left, 0);
  val true_eq_true = JClause.subterm_at_full_pos c true_eq_true_position;
  val [conclusion] = Jeha.simp_bool_rw @{context} c true_eq_true_position;
  (* val () = writeln (JClause.pretty_clause @{context} conclusion); *)
  val simplified_term = JClause.subterm_at_full_pos conclusion true_eq_true_position;
  \<^assert> (simplified_term aconv @{term "True"});
\<close>

ML_val \<open>
  val c = JClause.of_term (@{term_schem "(True \<longrightarrow> False) = d"}, 0);
  val true_imp_false_position = ([], JLit.Left, 0);
  val [conclusion] = Jeha.simp_bool_rw @{context} c true_imp_false_position;
  val simplified_term = JClause.subterm_at_full_pos conclusion true_imp_false_position;
  \<^assert> (simplified_term aconv @{term "False"});
\<close>

end