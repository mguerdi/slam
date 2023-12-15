theory simp_normalize_negative_pred_lit

imports "test_base"

begin

ML_val \<open>
  val c = JClause.of_term (@{term "True \<noteq> False"}, 1);
  val SOME c' = Jeha.simp_normalize_pred_lits c;
  val expected = JClause.of_term (@{term "False = False"}, 2);
  \<^assert> (JClause.term_of c' aconv JClause.term_of expected);
\<close>

end