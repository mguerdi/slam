theory jeha_test

imports Main

begin

(* Antiquotations for term and type patterns from the cookbook. *)
ML \<open>
  val term_pat_setup =
  let
    val parser = Args.context -- Scan.lift Parse.embedded_inner_syntax

    fun term_pat (ctxt, str) =
      str |> Proof_Context.read_term_pattern ctxt |> ML_Syntax.print_term |> ML_Syntax.atomic
  in
    ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat)
  end

  val type_pat_setup =
  let
    val parser = Args.context -- Scan.lift Parse.embedded_inner_syntax

    fun typ_pat (ctxt, str) =
      let
        val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
      in
        str |> Syntax.read_typ ctxt' |> ML_Syntax.print_typ |> ML_Syntax.atomic
      end
  in
    ML_Antiquotation.inline @{binding "typ_pat"} (parser >> typ_pat)
  end
\<close>

setup \<open> term_pat_setup \<close>

setup \<open> type_pat_setup \<close>

ML \<open>
  fun verbose_of ctxt = config_put_many_bool ctxt
    [show_types, show_brackets, show_markup, (* show_sorts, *) show_structs]
  and config_put_many_bool ctxt options =
    List.foldr (fn (option, ctxt) => Config.put option true ctxt) ctxt options
  fun pretty_term ctxt t = Syntax.pretty_term ctxt t |> Pretty.string_of
  fun pretty_terms ctxt terms =
    terms
    |> map (Syntax.pretty_term ctxt)
    |> Pretty.commas |> Pretty.block |> Pretty.string_of
  fun pretty_type ctxt typ = Pretty.string_of (Syntax.pretty_typ ctxt typ)
\<close>

ML \<open>
  local
    fun pp_pair (x, y) = Pretty.list "(" ")" [x, y]
    fun pp_triple (x, y, z) = Pretty.list "(" ")" [x, y, z]
    fun pp_list xs = Pretty.list "[" "]" xs
    fun pp_str s = Pretty.str s
    fun pp_qstr s = Pretty.quote (pp_str s)
    fun pp_int i = pp_str (string_of_int i)
    fun pp_sort S = pp_list (map pp_qstr S)
    fun pp_constr a args = Pretty.block [pp_str a, Pretty.brk 1, args]
  in
  fun raw_pp_typ (TVar ((a, i), S)) = pp_constr "TVar" (pp_pair (pp_pair (pp_qstr a, pp_int i), pp_sort S))
  | raw_pp_typ (TFree (a, S)) = pp_constr "TFree" (pp_pair (pp_qstr a, pp_sort S))
  | raw_pp_typ (Type (a, tys)) =  pp_constr "Type" (pp_pair (pp_qstr a, pp_list (map raw_pp_typ tys)))
  fun raw_pp_term  (Const (c, T)) = pp_constr "Const" (pp_pair (pp_qstr c, raw_pp_typ T))
    | raw_pp_term (Free (x, T)) = pp_constr "Free" (pp_pair (pp_qstr x, raw_pp_typ T))
    | raw_pp_term (Var ((x, i), T)) = pp_constr "Var" (pp_pair (pp_pair (pp_qstr x, pp_int i), raw_pp_typ T))
    | raw_pp_term (Bound i) = pp_constr "Bound" (pp_int i)
    | raw_pp_term (Abs(x, T, t)) = pp_constr "Abs" (pp_triple (pp_qstr x, raw_pp_typ T, raw_pp_term t))
    | raw_pp_term (s $ t) = pp_constr "$" (pp_pair (raw_pp_term s, raw_pp_term t))
  end;
  ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_pp_typ);
  ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_pp_term);
  val some_typ = @{typ "'a \<Rightarrow> 'b"}
  val _ = writeln (pretty_type @{context} some_typ)
  val list_typ = @{typ "'a list"}
  val _ = writeln (pretty_type @{context} some_typ)
  val bool_typ = @{typ "bool"}
  val int_typ = @{typ "int"}
  val _ = writeln (pretty_type @{context} (Type ("Int.int", [])));
  (* reset to default pretty printer *)
  ML_system_pp (fn depth => fn _ => ML_Pretty.to_polyml o Pretty.to_ML depth o Proof_Display.pp_typ Theory.get_pure);
  ML_system_pp (fn depth => fn _ => ML_Pretty.to_polyml o Pretty.to_ML depth o Proof_Display.pp_term Theory.get_pure);
\<close>

declare [[ML_debugger = true]]
declare [[ML_exception_trace = true]]
declare [[ML_exception_debugger = true]]

ML_file_debug \<open>jeha_common.ML\<close>
ML_file_debug \<open>jeha_lang.ML\<close>
ML_file_debug \<open>jeha_order.ML\<close>
ML_file_debug \<open>jeha.ML\<close>
ML_file_debug \<open>jeha_tactic.ML\<close>

ML \<open>
\<close>

ML \<open>
  fun pretty_green_nongreen_subterms ctxt term =
    let
      val tposs = Jeha_Lang.green_tposs_of term;
      val green_subterms = map (Jeha_Lang.subterm_at_tpos term) tposs;
      val non_green_subterms = Jeha_Lang.fold_non_greens cons term [];
    in
      "term:\t\t" ^ pretty_term ctxt term ^ "\ngreens:\t\t" ^ pretty_terms ctxt green_subterms ^
      "\nnongreens:\t" ^ pretty_terms @{context} non_green_subterms
    end;
  writeln (pretty_green_nongreen_subterms @{context} @{term_pat "f (g (\<not> p)) (\<forall> x . q) (?y a) (\<lambda> x . h b)"});
  fun pretty_normed_unnormed ctxt term =
    let val normed = Jeha_Lang.norm_quantifier_poly_eq term in
    "Q\<^sub>\<approx>: " ^ pretty_term ctxt term ^ "  \<mapsto>  " ^ pretty_term ctxt normed end;
  val no_rewrite_tests = [@{term "\<lambda> y . \<exists> x . g x y (z y) (f x)"}];
  val rewrite_tests = [@{term "\<exists> x . x a"}, Const (@{const_name "HOL.Ex"}, @{typ "('a \<Rightarrow> bool) \<Rightarrow> bool"}), @{term "\<forall> x . f (\<lambda> y . x)"}];
  (* Question: Why does a lone quantifier not make sense to isabelle? (can't be parsed using @{term ...}) *)
  (* writeln "Q\<^sub>\<approx>:"; pwrite_term @{context} unnormed; pwrite_term @{context} normed; *)
  writeln "shouldn't rewrite:";
  map (writeln o pretty_normed_unnormed @{context}) no_rewrite_tests;
  writeln "should rewrite:";
  map (writeln o pretty_normed_unnormed @{context}) rewrite_tests;
  writeln "Making Higher-Order Superposition work, Example 5:";
  writeln (pretty_green_nongreen_subterms @{context} @{term_pat "?F a \<and> p (\<forall> x . q x) b"});
  writeln (pretty_term @{context} (HOLogic.mk_not (HOLogic.mk_eq (@{term "a::'a"}, @{term "b::'a"}))));
\<close>

(* sup tests *)
ML \<open>
  (* part of Example 25 from o\<lambda>Sup paper (WORKS) *)
  val (a, b, w) = (@{term "a::'a"}, @{term "b::'a"}, @{term_pat "?w::'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"});
  val cs = Jeha.infer_sup @{context} ([(w $ a $ b $ b, w $ b $ a $ b, true)], (Jeha_Lang.Left, 0)) ([(a, b, false)], ([], Jeha_Lang.Right, 0));
  writeln (pretty_terms @{context} (map Jeha_Lang.term_of_clause cs));
  (* part of Example 27 from the o\<lambda>Sup paper (WORKS) *)
  val (a, b, h, g) = (@{term "a::'a"}, @{term "b::'a"}, @{term "h::'b \<Rightarrow> 'c"}, @{term "g::bool \<Rightarrow> 'c"})
  val (x2, x3) = (@{term_pat "?x2 :: 'a \<Rightarrow> 'd"}, @{term_pat "?x3 :: 'a \<Rightarrow> 'd"});
  (* val d = [((h $ (g $ (HOLogic.mk_eq (x2 $ a, x3 $ a)))), h $ (g $ @{term True}), false), (@{term False}, @{term True}, true), (x2 $ b, x3 $ b, true)];
  val d_term = Jeha.term_of_clause d; *)
  val d = Jeha_Lang.clause_of @{term_pat "h(g(?x2 a = ?x3 a)) \<noteq> h(g(True)) \<or> False = True \<or> ?x2 b = ?x3 b"};
  (* writeln ("D_anti: " ^ pretty_term @{context} d_anti);
  writeln ("D_anti_clause: " ^ pretty_term @{context} (Jeha_Lang.term_of_clause (Jeha_Lang.clause_of d_anti))); *)
  writeln ("D: " ^ pretty_term @{context} (Jeha_Lang.term_of_clause d));
  val c = [(a, b, false)];
  writeln ("C: " ^ pretty_term @{context} (Jeha_Lang.term_of_clause c));
  val cs = Jeha.infer_sup @{context} (d, (Jeha_Lang.Left, 2)) (c, ([], Jeha_Lang.Right, 0));
  val cs_terms = map Jeha_Lang.term_of_clause cs;
  writeln (pretty_terms (verbose_of @{context}) (map Jeha_Lang.term_of_clause cs));
\<close>

declare [[jeha_trace = true]]

ML \<open>
  fun pretty_thm_no_vars ctxt thm =
    let
      val ctxt' = Config.put show_question_marks false ctxt
    in
      pretty_term ctxt' (Thm.prop_of thm)
    end

  fun my_print_tac ctxt thm =
    let
      val _ = writeln "tracing"
      val _ = tracing (pretty_thm_no_vars ctxt thm)
    in
      Seq.single thm
    end
\<close>

(* lemma
  shows "x \<Longrightarrow> x"
apply(tactic \<open>my_print_tac @{context}\<close>)
apply(tactic \<open>assume_tac @{context} 0\<close>) *)

(* lemma test:
  shows "(x = y) \<longrightarrow> (y = z) \<longrightarrow> (x = z)"
  apply(tactic \<open>my_print_tac @{context}\<close>) *)

ML \<open>
  (* val eq_trans = Thm.prop_of @{thm test}
  val (axioms, conjecture) = Logic.strip_prems (2, [], eq_trans)
  val clauses = HOLogic.mk_not (Object_Logic.atomize_term @{context} conjecture) :: map (Object_Logic.atomize_term @{context}) axioms *)
  val clauses = map Jeha_Lang.clause_of [@{term "x = y"}, @{term "y = z"}, @{term "x \<noteq> z"}]
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) (map Jeha_Lang.term_of_clause clauses))
  val whatisthis = false andalso false orelse true
  val andthiswhat = true orelse false andalso false
  val result = Jeha.given_clause_loop @{context} 12 (Jeha.passive_set_of_list clauses) []
\<close>

ML \<open>
  val x_ord_x = Jeha_Order.kbo (@{term_pat "?x"}, @{term_pat "?x"})
  val x_ord_y = Jeha_Order.kbo (@{term_pat "?x"}, @{term_pat "?y"})
  val c_ord_c = Jeha_Order.kbo (@{term "x"}, @{term "x"})
  val o4 = Jeha_Order.kbo (@{term "\<forall>x. P x"}, @{term "P True"})
\<close>

(*
notepad
begin

  fix a::'a
  fix b::'a
  fix g::"bool \<Rightarrow> 'b"
  fix h::"'b \<Rightarrow> 'c"

  (* term "h(g(x'' a = x''' a)) \<noteq> h(g(True)) \<or> False = True \<or> x'' b = x''' b" *)

  let ?t = "h(g(x'' a = x''' a)) \<noteq> h(g(True)) \<or> False = True \<or> x'' b = x''' b"

  term ?t
end
*)
