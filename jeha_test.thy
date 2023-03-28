theory jeha_test

imports Main

begin

ML_file jeha.ML

ML \<open>
  fun pwrite_term ctxt t = Pretty.writeln (Syntax.pretty_term ctxt t)
  fun pwrite_terms ctxt terms =
    terms
    |> map (Syntax.pretty_term ctxt)
    |> Pretty.commas |> Pretty.block |> Pretty.writeln
\<close>

ML \<open>
  val quick_sig = ["a", "b", "f", "g", "h", "p", "q"]
  fun free_to_const (t as (Free (name, T))) = if exists (curry (op =) name) quick_sig then Const (name, T) else t
    | free_to_const t = t
  fun const_to_free (t as (Const (name, T))) = if exists (curry (op =) name) quick_sig then Free (name, T) else t
    | const_to_free t = t
  fun pwrite_quicksig ctxt = pwrite_term ctxt o (map_aterms const_to_free);
  val term_with_subterms = @{term "f (g (\<not> p)) (\<forall> x . q) (y a) (\<lambda> x . h b)"};
  pwrite_term @{context} term_with_subterms;
  val tposs = Jeha.green_tposs_of (map_aterms free_to_const term_with_subterms);
  val green_subterms = map (Jeha.subterm_at_tpos term_with_subterms) tposs;
  fun pwrite_term_quicksig ctxt = pwrite_term ctxt o (map_aterms const_to_free);
  fun pwrite_terms_quicksig ctxt = pwrite_terms ctxt o (map (map_aterms const_to_free));
  writeln "greens:"; map (pwrite_term_quicksig @{context}) green_subterms;
  val non_green_subterms = Jeha.fold_non_greens cons (map_aterms free_to_const term_with_subterms) [];
  writeln "nongreens:"; map (pwrite_term_quicksig @{context}) non_green_subterms;
  (* val unnormed = @{term "\<lambda> y . \<exists> x . g x y (z y) (f x)"}; (* don't rewrite: WORKS *) *)
  (* Question: Why does a lone quantifier not make sense to isabelle? (can't be parsed using @{term ...} *)
  val unnormed = Const (@{const_name "HOL.Ex"}, @{typ "('a \<Rightarrow> bool) \<Rightarrow> bool"}) (* rewrite: WORKS *)
  (* val unnormed = @{term "\<exists> x . x a"}; (* rewrite: WORKS *) *)
  (* val unnormed = @{term "\<forall> x . f (\<lambda> y . x)"} (* rewrite: WORKS *); *)
  val normed = map_aterms const_to_free (Jeha.norm_quantifier_poly_eq (map_aterms free_to_const unnormed));
  writeln "Q\<^sub>\<approx>:"; pwrite_term @{context} unnormed; pwrite_term @{context} normed;
  fun pwrite_green_non_green_poss ctxt term =
    let
      val tposs = Jeha.green_tposs_of (map_aterms free_to_const term);
      val green_subterms = map (Jeha.subterm_at_tpos term) tposs;
      val non_green_subterms = Jeha.fold_non_greens cons (map_aterms free_to_const term) [];
    in
      writeln "term:"; pwrite_term ctxt term; writeln "greens:"; pwrite_terms_quicksig ctxt green_subterms;
      writeln "nongreens:"; pwrite_terms_quicksig @{context} non_green_subterms
    end;
  (* Making Higher-Order Superposition work, Example 5 *)
  pwrite_green_non_green_poss @{context} @{term "F a \<and> p (\<forall> x . q x) b"}
\<close>