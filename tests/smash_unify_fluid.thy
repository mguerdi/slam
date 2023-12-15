theory smash_unify_fluid

imports "test_base"

begin

declare [[show_types]]

ML_val \<open>
  (* a lambda expression t, s.t. there exists a substitution \<sigma> s.t. t\<sigma> is \<eta>-contractible *)
  val fluid_lambda = @{term_schem "(\<lambda> x. ?x x d) :: 'a \<Rightarrow> 'b"};
  val var_and_const = @{term_schem "(?y c) :: 'a \<Rightarrow> 'b"} 
  val unifiers =
    Unify.unifiers
      ( (Context.Proof @{context})
      , Envir.init
      , [(fluid_lambda, var_and_const)]
      )
  val SOME ((unifier, ff_pairs), unifiers) = Seq.pull unifiers
  val [(l, r)] = ff_pairs;
  (* val SOME for_x = Envir.lookup unifier (("x", 0), @{typ "'a \<Rightarrow> 'b"})
  val _ = writeln (Jeha_Common.pretty_term @{context} for_x) *)
\<close>

end 