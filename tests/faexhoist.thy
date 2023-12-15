theory faexhoist

imports "../jeha"

begin

(* TODO
check that unification with
  \<forall> ?y
is the same as with the eta-expanded
  \<forall> x. ?y x
If not, then one of the two is hopefully more general. Which one? *)

ML_val \<open>
  val ctxt = @{context}
  val fresh_typ = TVar (("'a", 1), Sign.defaultS (Proof_Context.theory_of ctxt));
  val fresh_predicate = Var (("y_faexhoist", 1), fresh_typ --> @{typ bool});
  val forall_app_var = HOLogic.all_const fresh_typ $ fresh_predicate;
  \<^assert> (
    (Jeha_Unify.smash_unifiers (Context.Proof ctxt) [(forall_app_var, @{term "\<forall>x . p x"})] Envir.init)
    |> Seq.pull
    |> is_some
  );
\<close>

end
