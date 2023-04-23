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
ML_file_debug \<open>jeha_subsumption.ML\<close>
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
(*
lemma
  shows "x \<Longrightarrow> x"
(* by jeha *)
(* Question: why is this being called twice? *)
apply(tactic \<open>my_print_tac @{context}\<close>)
(*
apply(tactic \<open>assume_tac @{context} 1\<close>)
*)
*)

lemma test:
  shows "(x = y) \<Longrightarrow> (y = z) \<Longrightarrow> (x = z)"
  by jeha
(* apply(tactic \<open>my_print_tac @{context}\<close>) *)

lemma
  shows "(1 :: nat) + 1 = 2"
  by (jeha Num.nat_1_add_1)

datatype 'a bt =
    Lf
  | Br 'a  "'a bt"  "'a bt"

primrec n_nodes :: "'a bt \<Rightarrow> nat" where
  "n_nodes Lf = 0"
| "n_nodes (Br a t1 t2) = Suc (n_nodes t1 + n_nodes t2)"

primrec n_leaves :: "'a bt => nat" where
  "n_leaves Lf = Suc 0"
| "n_leaves (Br a t1 t2) = n_leaves t1 + n_leaves t2"

primrec depth :: "'a bt => nat" where
  "depth Lf = 0"
| "depth (Br a t1 t2) = Suc (max (depth t1) (depth t2))"

primrec reflect :: "'a bt => 'a bt" where
  "reflect Lf = Lf"
| "reflect (Br a t1 t2) = Br a (reflect t2) (reflect t1)"

primrec bt_map :: "('a => 'b) => ('a bt => 'b bt)" where
  "bt_map f Lf = Lf"
| "bt_map f (Br a t1 t2) = Br (f a) (bt_map f t1) (bt_map f t2)"

primrec preorder :: "'a bt => 'a list" where
  "preorder Lf = []"
| "preorder (Br a t1 t2) = [a] @ (preorder t1) @ (preorder t2)"

primrec inorder :: "'a bt => 'a list" where
  "inorder Lf = []"
| "inorder (Br a t1 t2) = (inorder t1) @ [a] @ (inorder t2)"

primrec postorder :: "'a bt => 'a list" where
  "postorder Lf = []"
| "postorder (Br a t1 t2) = (postorder t1) @ (postorder t2) @ [a]"

primrec append :: "'a bt => 'a bt => 'a bt" where
  "append Lf t = t"
| "append (Br a t1 t2) t = Br a (append t1 t) (append t2 t)"

lemma n_leaves_reflect: "n_leaves (reflect t) = n_leaves t"
proof (induct t)
  case Lf thus ?case
  proof -
    let "?p\<^sub>1 x\<^sub>1" = "x\<^sub>1 \<noteq> n_leaves (reflect (Lf::'a bt))"
    have "\<not> ?p\<^sub>1 (Suc 0)" by (jeha reflect.simps(1) n_leaves.simps(1))
    hence "\<not> ?p\<^sub>1 (n_leaves (Lf::'a bt))" by (jeha n_leaves.simps(1))
    thus "n_leaves (reflect (Lf::'a bt)) = n_leaves (Lf::'a bt)" by jeha
  qed
next
  case (Br a t1 t2) thus ?case
    by (jeha n_leaves.simps(2) add.commute reflect.simps(2))
qed



ML \<open>
  (* lazyness seems to work just fine... *)
  val number_seq = Seq.of_list [1, 2, 3, 4]
  val printing_seq = Seq.map (writeln o @{make_string}) number_seq
  val SOME (_, printed_one)  = let val _ = writeln "pull:" in Seq.pull printing_seq end
  val printed_two = writeln "pull again:"; Seq.pull printed_one;
  val first_three = Seq.take 3 printing_seq
  val _ = writeln "pull from first three:"; Seq.pull first_three;
  val even_printing_seq = Seq.map (writeln o @{make_string}) (Seq.map_filter (fn n => if n mod 2 = 0 then SOME n else NONE) number_seq)
  val _ = writeln "pull even:"; Seq.pull even_printing_seq;
\<close>

ML \<open>
  (* val eq_trans = Thm.prop_of @{thm test}
  val (axioms, conjecture) = Logic.strip_prems (2, [], eq_trans)
  val clauses = HOLogic.mk_not (Object_Logic.atomize_term @{context} conjecture) :: map (Object_Logic.atomize_term @{context}) axioms *)
  val clauses = map Jeha_Lang.clause_of [@{term "x = y"}, @{term "y = z"}, @{term "x \<noteq> z"}]
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) (map Jeha_Lang.term_of_clause clauses))
  val result = Jeha.given_clause_loop @{context} 12 (Jeha.passive_set_of_list clauses) []
\<close>

ML \<open>
  val f = @{term "f :: 'a \<Rightarrow> 'a"}
  val var_x = Var (("x", 0), @{typ "'a"})
  val f_is_id = HOLogic.mk_eq (f $ var_x, var_x)
  val clauses = map Jeha_Lang.clause_of [f_is_id, @{term "f (f y) \<noteq> y"}]
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) (map Jeha_Lang.term_of_clause clauses))
  val result = Jeha.given_clause_loop @{context} 5 (Jeha.passive_set_of_list clauses) []
\<close>

ML \<open>
  val zero = @{term "z :: 'a"}
  val s = @{term "s :: 'a \<Rightarrow> 'a"}
  val plus = @{term "p :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"}
  val var_x = Var (("x", 0), @{typ "'a"})
  val var_y = Var (("y", 0), @{typ "'a"})
  val zero_right_neutral = HOLogic.mk_eq (plus $ var_x $ zero, var_x)
  val plus_def = HOLogic.mk_eq (plus $ var_x $ (s $ var_y), s $ (plus $ var_x $ var_y))
  val two_neq_one_plus_one = @{term "s (s z) \<noteq> p (s z) (s z)"}
  val clauses = map Jeha_Lang.clause_of [zero_right_neutral, plus_def, two_neq_one_plus_one]
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) (map Jeha_Lang.term_of_clause clauses))
  (* FIXME: looks like some rewriting steps are missing pretty early on *)
  val result = Jeha.given_clause_loop @{context} 12 (Jeha.passive_set_of_list clauses) []
\<close>

(* Baader, Nipkow Example 7.1.1 (central groupoids) *)
ML \<open>
  val t = @{term "t :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"}
  val var_x = Var (("x", 0), @{typ "'a"})
  val var_y = Var (("y", 0), @{typ "'a"})
  val var_z = Var (("z", 0), @{typ "'a"})
  val eq = HOLogic.mk_eq (t $ (t $ var_x $ var_y) $ (t $ var_y $ var_z), var_y)
  (* one of the rules in the completed rewrite system *)
  val xxyz_neq_xy = HOLogic.mk_not (HOLogic.mk_eq (t $ var_x $ (t $ (t $ var_x $ var_y) $ var_z), t $ var_x $ var_y))
  val clauses = map Jeha_Lang.clause_of [eq, xxyz_neq_xy]
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) (map Jeha_Lang.term_of_clause clauses))
  val result = Jeha.given_clause_loop @{context} 5 (Jeha.passive_set_of_list clauses) []
\<close>

ML \<open>
  val c1 = @{term "P a :: bool"}
  val c2 = @{term "a = b"}
  val c3 = @{term "\<not> P b"}
  val clauses = map Jeha_Lang.clause_of [c1, c2, c3]
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) (map Jeha_Lang.term_of_clause clauses))
  val result = Jeha.given_clause_loop @{context} 10 (Jeha.passive_set_of_list clauses) []
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
