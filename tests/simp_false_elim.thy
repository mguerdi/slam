theory simp_false_elim

imports "test_base"

begin

(* This was the simp_bool_outer_claus bug where the condition that the head of s
may not be a logical symbol wasn't handled. *)
ML_val \<open>
  val c = JClause.of_term (@{term_schem "?x b = True \<or> (?x a = True) = False"}, 1);
  val (lpos, cpos) = (JLit.Left, 0);
  val bad = Jeha.simp_false_elim @{context} c (lpos, cpos);
  val lit = JClause.lit_at cpos c;
  val (s, b) = lit |> JLit.dest_pred ||> Jeha.ml_bool_of;
  val c' = JClause.delete_lit_at cpos c;
  val bad_direct = Jeha.outer_clausify b s c;
\<close>

ML_val \<open>
  val good = JClause.of_term (@{term_schem "?x b = True \<or> (?x a = True) = False"}, 1);
  val simplified = Jeha.simp_false_elim @{context} good (JLit.Left, 0);
  \<^assert> (null simplified);
\<close>

end