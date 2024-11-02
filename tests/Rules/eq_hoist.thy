theory eq_hoist

imports "JEHA_TEST_BASE.test_base"

begin

ML_val \<open>
  (* from o\<lambda>Sup example 25 *)
  (* side condition 4. *)
  val c = JClause.of_term (@{term_schem "(?z a = False) \<or> (?z b = True)"}, 1);
  val [conclusion] = Jeha.infer_eq_hoist @{context} c ([], JLit.Left, 0);
  val conclusion_term = JClause.term_of conclusion
  val expected = @{term_schem "False = False \<or> (?x4 b = ?y_eqneqhoist3 b) = True \<or> (?x4 :: 'a \<Rightarrow> ?'a1) a = ?y_eqneqhoist3 a"};
  (* val () = writeln (Jeha_Common.pretty_term @{context} conclusion_term);
  val () = writeln (Jeha_Common.pretty_term @{context} expected); *)
  \<^assert> (expected aconv conclusion_term);
\<close>

ML_val \<open>
  (* EqHoist can emulate NeqHoist *)
  val c = JClause.of_term (@{term_schem "f (\<not> ((a :: 'a) = b)) = d"}, 1);
  val [conclusion] = Jeha.infer_eq_hoist @{context} c ([1, 1], JLit.Left, 0);
  val conclusion_term = JClause.term_of conclusion;
  val expected = @{term_schem "f (\<not> False) = d \<or> (a :: 'a) = b"};
  (* val () = writeln (Jeha_Common.pretty_term @{context} conclusion_term);
  val () = writeln (Jeha_Common.pretty_term @{context} expected); *)
  \<^assert> (expected aconv JClause.term_of conclusion);
\<close>

end
