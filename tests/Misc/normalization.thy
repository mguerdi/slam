theory normalization

imports "JEHA_TEST_BASE.test_base"

begin

declare [[show_types]]

ML \<open>
  val Ta = @{typ "'a"};
  val b = @{term "b :: 'a"};
  val f = @{term "f :: 'b \<Rightarrow> HOL.bool \<Rightarrow> 'a \<Rightarrow> HOL.bool"};
  val t = HOLogic.all_const Ta $ (f $ Abs ("x", @{typ "'b"}, (HOLogic.all_const Ta $ (HOLogic.eq_const Ta $ b))));
  val t_normed = JTerm.norm_beta_eta_qeta_env (Envir.init) t;
  val befor = @{term_schem "((\<forall>(x::bool). ((?f10 x)                    = (\<lambda>(a::?'a12::type). x))) = False)"};
  val after = @{term        "((\<forall>(x::bool). ((\<lambda>(a::bool). (All ((=) a))) = (\<lambda>(a::bool). x))       ) = False)"};
  val after_normed = JTerm.norm_beta_eta_qeta_env (Envir.init) after;
  val () = writeln (Jeha_Common.pretty_term @{context} befor);
  val () = writeln (Jeha_Common.pretty_term @{context} after);
  val () = writeln (Jeha_Common.pretty_term @{context} after_normed);
  (* FIXME: make an assertion *)
\<close>

end
