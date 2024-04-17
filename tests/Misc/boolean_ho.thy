theory boolean_ho

imports "JEHA_TEST_BASE.test_base"

begin

ML_val \<open>
  val c = JClause.of_term (@{term_schem "(\<forall> x. ?y x = (p x \<and> q x)) = False"}, 0);
  val forall_subterm_position = ([], JLit.Left, 0);
  val forall_subterm = JClause.subterm_at_full_pos c forall_subterm_position;
  val [conclusion] = Jeha.infer_forall_rw @{context} c forall_subterm_position; 
  val instead_of_forall = JClause.subterm_at_full_pos conclusion forall_subterm_position;
  val skolem = @{term_schem "SOME z. \<not> (?y z = (p z \<and> q z))"};
  val lambda = JTerm.subterm_at forall_subterm [1];
  val expected = JTerm.norm_beta_eta_qeta (lambda $ skolem);
  (* val () = writeln (Jeha_Common.pretty_term @{context} expected);
  val () = writeln (Jeha_Common.pretty_term @{context} instead_of_forall); *)
  \<^assert> (expected aconv instead_of_forall);
\<close>

end