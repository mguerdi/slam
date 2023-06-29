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

(* declare [[ML_debugger = true]]
declare [[ML_exception_trace = true]]
declare [[ML_exception_debugger = true]] *)

ML_file(*_debug*) \<open>jeha_common.ML\<close>
ML_file(*_debug*) \<open>clause_id.ML\<close>
ML_file(*_debug*) \<open>jterm.ML\<close>
ML_file(*_debug*) \<open>jeha_order.ML\<close>
ML_file(*_debug*) \<open>jlit.ML\<close>
ML_file(*_debug*) \<open>jclause_pos.ML\<close>
ML_file(*_debug*) \<open>jeha_log.ML\<close>
ML_file(*_debug*) \<open>jclause.ML\<close>
ML_file(*_debug*) \<open>jeha_unify.ML\<close>
ML_file(*_debug*) \<open>jeha_subsumption.ML\<close>
ML_file(*_debug*) \<open>jeha.ML\<close>
ML_file(*_debug*) \<open>jeha_tactic.ML\<close>

ML \<open>
  val idxs_of_max = Jeha_Order.idxs_of_maximal_elements (SOME o int_ord)
  val one = idxs_of_max [3, 1, 7, 2, 3]
  val rules = Jeha.bool_rw_non_var_rules 
\<close>

ML \<open>
  val asdwef = @{term undefined}
  fun cposs_of_dups ls =
    fold_index
      (fn (i, l) => fn (dup_is, head_list) =>
        if exists (curry (op =) l) head_list
          (* duplicate of l has already been seen *)
          then (i::dup_is, head_list)
          (* l is new, add it to the seen lits *)
          else (dup_is, l::head_list))
      ls
      ([], [])
  val thedupindexes = cposs_of_dups [5, 1, 2, 1, 7, 7, 2, 5]
  val x_var = @{term_pat "?x::?'a"}
  val y_var = @{term_pat "?y::?'a"}
  val z_var = @{term_pat "?z::?'a"}
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) [x_var, y_var, z_var])
  val unit_clause = JClause.of_term ((HOLogic.mk_eq (x_var, y_var)), 0)
  val lp = JLit.Right
  val j = ([], JLit.Left, 0)
  val target_clause = JClause.of_term ((HOLogic.mk_eq (z_var, x_var)), 1)
  val unit_clause = JClause.incr_indexes (JClause.maxidx target_clause + 1) unit_clause
  val (from, to) = apply2 (JLit.term_at_lpos (the_single (JClause.literals unit_clause))) (lp, JLit.swap_lpos lp) (* Schulz: (s, t) *)
  val _ = writeln ("from, to renamed" ^ Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) [from, to])
  val target_term = JClause.subterm_at_full_pos target_clause j (* Schulz: u *)
  val matchers =
    Jeha_Unify.matchers
      (Context.Proof @{context})
      (JClause.maxidx_of2 (unit_clause, target_clause))
      [(from, target_term)]
  val SOME (matcher, _) = Seq.pull matchers
  val _ = writeln (Jeha_Common.pretty_tyenv (Jeha_Common.verbose_of @{context}) (Envir.type_env matcher))
  val _ = writeln (Jeha_Common.pretty_tenv (Jeha_Common.verbose_of @{context}) (Envir.term_env matcher))
  (* works *)
  val (from', to') = apply2 (JTerm.norm_beta_eta_qeta_env matcher) (from, to)
  (* val a_subst = Envir.subst_type (Envir.type_env matcher) @{typ_pat "?'a"} *)
  (* val (from, to) =
    apply2 (Envir.subst_term (Envir.type_env matcher, Envir.term_env matcher)) (from, to) *)
  (* doesn't *)
  (* val (from, to) = apply2 (JTerm.norm_beta_eta_qeta_env matcher) (from, to) *)
  (* val from = JTerm.norm_beta_eta_qeta_env matcher x_var *)

  (* val x_var_subst = Envir.norm_term matcher @{term_pat "c::'a"} *)
  val _ = writeln "hello"
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) [from, to])
  val _ = writeln "bye"
\<close>


ML \<open>
  fun pretty_green_nongreen_subterms ctxt term =
    let
      val tposs = JTerm.green_tposs_of term;
      val green_subterms = map (JTerm.subterm_at term) tposs;
      val non_green_subterms = JTerm.fold_non_greens cons term [];
    in
      "term:\t\t" ^ pretty_term ctxt term ^ "\ngreens:\t\t" ^ pretty_terms ctxt green_subterms ^
      "\nnongreens:\t" ^ pretty_terms @{context} non_green_subterms
    end;
  writeln (pretty_green_nongreen_subterms @{context} @{term_pat "f (g (\<not> p)) (\<forall> x . q) (?y a) (\<lambda> x . h b)"});
  fun pretty_normed_unnormed ctxt term =
    let val normed = JTerm.norm_quantifier_poly_eq term in
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
  val cs = Jeha.infer_sup @{context} (JClause.of_literals ([(w $ a $ b $ b, w $ b $ a $ b, true)], 0), (JLit.Left, 0)) (JClause.of_literals ([(a, b, false)], 1), ([], JLit.Right, 0));
  writeln (pretty_terms @{context} (map JClause.term_of cs));
  (* part of Example 27 from the o\<lambda>Sup paper (WORKS) *)
  val (a, b, h, g) = (@{term "a::'a"}, @{term "b::'a"}, @{term "h::'b \<Rightarrow> 'c"}, @{term "g::bool \<Rightarrow> 'c"})
  val (x2, x3) = (@{term_pat "?x2 :: 'a \<Rightarrow> 'd"}, @{term_pat "?x3 :: 'a \<Rightarrow> 'd"});
  (* val d = [((h $ (g $ (HOLogic.mk_eq (x2 $ a, x3 $ a)))), h $ (g $ @{term True}), false), (@{term False}, @{term True}, true), (x2 $ b, x3 $ b, true)];
  val d_term = Jeha.term_of_clause d; *)
  val d = JClause.of_term (@{term_pat "h(g(?x2 a = ?x3 a)) \<noteq> h(g(True)) \<or> False = True \<or> ?x2 b = ?x3 b"}, 2);
  (* writeln ("D_anti: " ^ pretty_term @{context} d_anti);
  writeln ("D_anti_clause: " ^ pretty_term @{context} (JClause.term_of (JClause.of_term d_anti))); *)
  writeln ("D: " ^ pretty_term @{context} (JClause.term_of d));
  val c = JClause.of_literals ([(a, b, false)], 3);
  writeln ("C: " ^ pretty_term @{context} (JClause.term_of c));
  val cs = Jeha.infer_sup @{context} (d, (JLit.Left, 2)) (c, ([], JLit.Right, 0));
  val cs_terms = map JClause.term_of cs;
  writeln (pretty_terms @{context} (map JClause.term_of cs));
\<close>

(* BoolHoist tests *)
ML \<open>
  val (unifier, maxidx) = Sign.typ_unify @{theory} (@{typ_pat "?'a"}, @{typ "HOL.bool"}) (Vartab.empty, 10)
\<close>

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
  by (jeha (dump) Num.nat_1_add_1)

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




declare [[jeha_trace = true]]

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
    (* takes 33 steps with order restrictions, ~210 steps without *)
    by (jeha n_leaves.simps(2) add.commute reflect.simps(2))
qed

declare [[jeha_trace = false]]


(*
ML \<open>
  val dumped_state = !Jeha_Tactic.dump;
  val dumped_states = length dumped_state;
  val (ctxt, countdown, passive, active) = nth dumped_state 0
  fun seq_of_passive_set passive =
    if Jeha.Passive_Set.is_empty passive
      then Seq.empty
      else Jeha.Passive_Set.min_elem passive ||> seq_of_passive_set |> uncurry Seq.cons
  (* val list_passive = Seq.list_of (seq_of_passive_set passive)
  val _ = writeln (Jeha_Common.pretty_terms @{context} (map JClause.term_of list_passive))
  val _ = writeln (Jeha_Common.pretty_terms @{context} (map JClause.term_of active)) *)
  val _ = Jeha.given_clause_loop false (Config.put Jeha_Common.trace true ctxt) 5 passive active (* handle TYPE (msg, _, ts) => error (msg ^ " " ^ (Jeha_Common.pretty_terms (verbose_of ctxt) ts)) *)
\<close>
*)


(*
(* debugging sup *)
ML \<open>
  val helper = JClause.of_term
    (@{term_pat "n_leaves (Br ?a ?t1.0 ?t2.0) = n_leaves ?t1.0 + n_leaves ?t2.0"}, 0)
  val target_clause = JClause.of_term
    (@{term_pat "n_leaves (reflect (Br a t1 t2)) \<noteq> n_leaves t1 + n_leaves t2"}, 1)
  val [inferred] = Jeha.infer_clauses @{context} [helper] target_clause
  val [cheap_simplified] = Jeha.forward_simplify @{context} true active inferred;
  Jeha.is_trivial cheap_simplified
\<close>
*)


(* debugging rewriting *)
ML \<open>
  (* val unit_clause = JClause.of_term
    (@{term_pat "reflect (Br ?a ?t1.0 ?t2.0) = Br ?a (reflect ?t2.0) (reflect ?t1.0)"}, 0)
  val target_clause = JClause.of_term
    (@{term_pat "n_leaves (reflect (Br a t1 t2)) \<noteq> n_leaves (Br a t1 t2)"}, 1) *)
  val unit_clause = JClause.of_term
    (@{term_pat "n_leaves (Br ?LRa ?LRt1.0 ?LRt2.0) = n_leaves ?LRt2.0 + n_leaves ?LRt1.0"}, 0)
  val target_clause = JClause.of_term
    (@{term_pat "n_leaves (reflect (Br a t1 t2)) \<noteq> n_leaves (Br ?LRa t2 t1)"}, 1)
  val order = Jeha_Order.kbo (@{term_pat "n_leaves (Br ?a t1 t2)"}, @{term_pat "n_leaves t2 + n_leaves t1"})
  (*
  val (positive, ctxt, (unit_clause, lp), (target_clause, j as (_, _, target_cp))) =
    (false, @{context}, (unit_clause, JLit.Left), (target_clause, ([1], JLit.Left, 0)))
  val rewritten = Jeha.impl_simp_rewrite_lits positive ctxt (unit_clause, lp) (target_clause, j)
  val body =
    (* check unit_clause *)
    if not (Jeha.is_pos_unit unit_clause) then NONE else
    (* check that to be rewritten literal is indeed positive / negative *)
    if not (positive = #3 (JClause.lit_at target_cp target_clause)) then NONE else
    let
      (* make variables distinct *)
      val unit_clause = JClause.map_literals (map (JLit.map (Jeha.prefix_Vars_TVars "L"))) unit_clause
      val target_clause = JClause.map_literals (map (JLit.map (Jeha.prefix_Vars_TVars "R"))) target_clause
      val (from, to) = apply2 (JLit.term_at_lpos (the_single (JClause.literals unit_clause))) (lp, JLit.swap_lpos lp) (* Schulz: (s, t) *)
      val target_term = JClause.subterm_at_full_pos target_clause j (* Schulz: u *)
      val matchers = Jeha_Unify.matchers (Context.Proof ctxt) [(from, target_term)]
      fun build_conclusion matcher =
        let
          val msg =  "   " ^ (if positive then "(RP)" else "(RN)")
            ^ " rewriting " ^ Jeha_Common.pretty_term ctxt target_term
            ^ " in " ^ JClause.pretty_clause ctxt target_clause
            ^ " with " ^ Jeha_Common.pretty_term ctxt from
            ^ " \<mapsto> " ^ Jeha_Common.pretty_term ctxt to
          (* NOTE: subst_term is only for Pattern.match, not Unify.matchers! *)
          val (from, to) = apply2 (JTerm.norm_beta_eta_qeta_env matcher) (from, to)
        in
          if SOME GREATER = Jeha_Order.kbo (from, to) (* Schulz: \<sigma>(s) > \<sigma>(t) *)
            then
              (* FIXME: understand and implement the restrictions on RP form Schulz's paper *)
              let
                val rewritten_clause = JClause.map_at_full_pos j (K to) target_clause
                val rewriting_clause = JClause.dummy [(from, to, true)]
                val rewriting_smaller_than_rewritten = (fn () =>
                  SOME LESS = Jeha_Order.clause_kbo (rewriting_clause, rewritten_clause))
              in
                if not positive orelse rewriting_smaller_than_rewritten ()
                  then (
                    Jeha_Common.trace_msg ctxt (fn () => msg);
                    (* writeln ("      " ^ (Jeha_Common.pretty_tenv ctxt (Envir.term_env matcher))); *)
                    SOME (JClause.map_literals (map (JLit.map JTerm.norm_beta_eta_qeta)) rewritten_clause))
                  else NONE
              end
            else
              (writeln "not greater"; NONE)
        end
    in
      let val SOME (matcher, _) = Seq.pull matchers in
        SOME (apply2 (JTerm.norm_beta_eta_qeta_env matcher) (from, to))
      end
      (* SOME (from, target_term) *)
      (* FIXME: print warning message when discarding unifiers? *)
      (* |> Seq.take 4
      |> Seq.map_filter build_conclusion
      |> Seq.pull *)
    end
    *)
\<close>

(* (* debugging equality subsumption *)
ML \<open>
  val comm = @{term_pat "?x + ?y = ?y + ?x"}
  (* val a_comm = @{term_pat "?a + (?b + ?c) = ?a + (?c + ?b)"} *)
  val a_comm = @{term_pat "?a + ?b + ?c = ?b + ?a + ?c"}
  val does_equality_subsume =
    Jeha.equality_subsumes @{context} (JClause.of_term (comm, 0), JClause.of_term (a_comm, 1))
  val can_match_single =
    Jeha.literal_can_match_single_disagreement @{context} (JLit.of_term comm) (JLit.of_term a_comm)
  
  val (ctxt, lit, target_lit) = (@{context}, JLit.of_term comm, JLit.of_term a_comm)
  val (lhs, rhs, true) = lit (* Schulz: s, t *)
  val (target_lhs, target_rhs, _) = target_lit (* Schulz: u[], u[]*)
  (* Schulz: p *)
  val single_disagreement_position = Jeha.find_single_green_disagreement ctxt (target_lhs, target_rhs)
  val (target_term_lhs, target_term_rhs) = (* u|\<^sub>p *)
    (JTerm.subterm_at target_lhs single_disagreement_position,
    JTerm.subterm_at target_rhs single_disagreement_position)
  (* FIXME: does matching need renaming or not? *)
  val exists_matcher =
    (Jeha_Unify.matchers (Context.Proof ctxt) ([(lhs, target_lhs), (rhs, target_rhs)]),
    Jeha_Unify.matchers (Context.Proof ctxt) ([(lhs, target_rhs), (rhs, target_lhs)]))
    |> Seq.interleave
    |> Seq.pull
    |> is_some


  val (left, right) = HOLogic.dest_eq a_comm
  val single_disagreement = Jeha.find_single_green_disagreement @{context} (left, right)
  val (target_term_lhs, target_term_rhs) = (* u|\<^sub>p *)
    (JTerm.subterm_at left single_disagreement,
    JTerm.subterm_at right single_disagreement)
  val (lhs, rhs) = HOLogic.dest_eq comm
  val matchers = Seq.interleave
    ( Jeha_Unify.matchers (Context.Proof @{context}) [(lhs, target_term_lhs), (rhs, target_term_rhs)]
    , Jeha_Unify.matchers (Context.Proof @{context}) [(rhs, target_term_lhs), (lhs, target_term_rhs)])
  val matcher = Seq.pull matchers
  val unifiers = Jeha_Unify.smash_unifiers (Context.Proof @{context}) [(left, right)] Envir.init
  val SOME (unifier, _) = Seq.pull unifiers
  val _ = writeln (Jeha_Common.pretty_tenv @{context} (Envir.term_env unifier))
  val affected_vars = Vartab.keys (Envir.term_env unifier)
  fun term_poss_of_affected_vars t =
    (* consider all positions in the term *)
    JTerm.green_tposs_of t
    (* filter out the ones that don't point to affected variables *)
    |> filter (fn tp =>
        case JTerm.subterm_at t tp of
          Var (x, _) => exists (curry (op =) x) affected_vars
        | _ => false)
  val adfdwqfsfqw = (left, right) |> apply2 (term_poss_of_affected_vars)
  val qwefpuoqwpe =
    (left, right)
    |> apply2 term_poss_of_affected_vars
    |> (op @)
    |> (fn tps => fold (fst oo curry (chop_common_prefix (op =))) tps [2, 2])
\<close>
*)


lemma n_nodes_reflect: "n_nodes (reflect t) = n_nodes t"
proof (induct t)
  case Lf thus ?case by (jeha reflect.simps(1))
next
  case (Br a t1 t2) thus ?case
    by (jeha add.commute n_nodes.simps(2) reflect.simps(2))
    (* ~146 steps with order restrictions *)
    (* 98 steps on 1099579 *)
qed

lemma depth_reflect: "depth (reflect t) = depth t"
apply (induct t)
 apply (jeha depth.simps(1) reflect.simps(1))
by (jeha depth.simps(2) max.commute reflect.simps(2))

text \<open>
The famous relationship between the numbers of leaves and nodes.
\<close>

lemma n_leaves_nodes: "n_leaves t = Suc (n_nodes t)"
apply (induct t)
 apply (jeha n_leaves.simps(1) n_nodes.simps(1))
by auto

lemma reflect_reflect_ident: "reflect (reflect t) = t"
apply (induct t)
 apply (jeha reflect.simps(1))
proof -
  fix a :: 'a and t1 :: "'a bt" and t2 :: "'a bt"
  assume A1: "reflect (reflect t1) = t1"
  assume A2: "reflect (reflect t2) = t2"
  have "\<And>V U. reflect (Br U V (reflect t1)) = Br U t1 (reflect V)"
    using A1 by (jeha reflect.simps(2))
  hence "\<And>V U. Br U t1 (reflect (reflect V)) = reflect (reflect (Br U t1 V))"
    by (jeha reflect.simps(2))
  hence "\<And>U. reflect (reflect (Br U t1 t2)) = Br U t1 t2"
    using A2 by jeha
  thus "reflect (reflect (Br a t1 t2)) = Br a t1 t2" by blast
qed

lemma bt_map_ident: "bt_map (%x. x) = (%y. y)"
apply (rule ext)
apply (induct_tac y)
 apply (jeha bt_map.simps(1))
by (jeha bt_map.simps(2))


(* debugging reused names in smash_unifiers *)
(*
ML \<open>
  val (t, u) =
    ( @{term_pat "Br ((?Lf::(?'La \<Rightarrow> ?'Lb)) (?La::?'La))"} (* (bt_map ?Lf (?Lt1.0::?'La bt)) (bt_map ?Lf (?Lt2.0::?'La bt))"} *)
    , @{term_pat "Br ((?Rf::(?'Ra \<Rightarrow> ?'Rb)) (?Ra::?'Ra))"} (* (bt_map ?Rf (?Rt1.0::?'Ra bt)) (bt_map ?Rf (?Rt2.0::?'Ra bt))"} *) )
  val unifiers = Jeha_Unify.unifiers (Context.Proof @{context}, Envir.init, [(t, u)])
  
  val SOME ((unifier, flex_flex), _) = Seq.pull unifiers
  val flex_flex_maxidx = fold (fn tu => fn maxidx => Int.max (maxidx, Int.max (apply2 maxidx_of_term tu))) flex_flex ~1
  val unifier = Envir.Envir { maxidx = Int.max (Envir.maxidx_of unifier, flex_flex_maxidx), tenv = Envir.term_env unifier, tyenv = Envir.type_env unifier }
  val smashed = Unify.smash_unifiers (Context.Proof @{context}) flex_flex unifier (* [(@{term_pat "(?f :: 'a \<Rightarrow> 'b) t"}, @{term_pat "(?g :: 'a \<Rightarrow> 'b) u"})] Envir.init *)
  val SOME (smash_result, _) = Seq.pull smashed
  val _ = writeln (Jeha_Common.pretty_tenv (Jeha_Common.verbose_of @{context}) (Envir.term_env smash_result))
  (* val _ = writeln (Jeha_Common.pretty_tyenv (Jeha_Common.verbose_of @{context}) (Envir.type_env unifier))
  val _ = writeln (Jeha_Common.pretty_tenv (Jeha_Common.verbose_of @{context}) (Envir.term_env unifier)) *)
\<close>
*)

(* FIXME: what should apply (jeha ...) do? *)
lemma bt_map_append: "bt_map f (append t u) = append (bt_map f t) (bt_map f u)"
apply (induct t)
 apply (jeha append.simps(1) bt_map.simps(1))
 (* takes ~130 steps *)
by (jeha append.simps(2) bt_map.simps(2))
 (* ~90 steps if the problem clauses are activated first *)
 (* 56 steps with order restrictions *)

ML \<open>
val ac = JClause.of_term (@{term_pat "((append (Br (?a::?'a) (?t1.0::?'a bt) (?t2.0::?'a bt)) (?t::?'a bt)) = (Br ?a (append ?t1.0 ?t) (append ?t2.0 ?t)))"}, 0)
val gc = JClause.of_term (@{term_pat "((bt_map (?f::(?'a \<Rightarrow> ?'b)) (Br (?a::?'a) (?t1.0::?'a bt) (?t2.0::?'a bt))) = (Br (?f ?a) (bt_map ?f ?t1.0) (bt_map ?f ?t2.0)))"}, 1)

val pc = JClause.of_term (@{term_pat "((bt_map (\<lambda>(a::?'a). (?f2::?'b)) (Br (?a::?'a) (?t1.0::?'a bt) (?t2.0::?'a bt))) = (bt_map (\<lambda>(a::?'a). ?f2) (Br (?a1::?'a) ?t1.0 ?t2.0)))"}, 2)

val inferred = Jeha.infer_clauses @{context} [gc] pc
val _ = writeln (JClause.pretty_clauses @{context} inferred)
\<close>

(*
ML \<open>
  val dumped_state = !Jeha_Tactic.dump;
  val dumped_states = length dumped_state;
  val (ctxt, countdown, passive, active) = nth dumped_state 0
  val _ = Jeha.given_clause_loop false (Jeha_Common.verbose_of ctxt) 4 passive active (* handle TYPE (msg, _, ts) => error (msg ^ " " ^ (Jeha_Common.pretty_terms (verbose_of ctxt) ts)) *)
\<close>
*)










(*

(* FIXME: needs clausification
*)
declare [[unify_search_bound = 10]]
lemma bt_map_compose: "bt_map (f o g) t = bt_map f (bt_map g t)"
apply (induct t)
 apply (jeha bt_map.simps(1))
by (jeha (dump) bt_map.simps(2) o_eq_dest_lhs)
(* takes an hour, prints Unification bound exceeded 19481 times*)

*)












(*
ML \<open>
  val dumped_state = !Jeha_Tactic.dump;
  val dumped_states = length dumped_state;
  val _ = writeln ("NUMBER OF DUMEPD STATES = " ^ @{make_string} dumped_states)
  val (ctxt, countdown, passive, active) = nth dumped_state 0
  fun seq_of_passive_set passive =
    if Jeha.Passive_Set.is_empty passive
      then Seq.empty
      else Jeha.Passive_Set.min_elem passive ||> seq_of_passive_set |> uncurry Seq.cons
  val list_passive = Seq.list_of (seq_of_passive_set passive)
  val _ = writeln (Jeha_Common.pretty_terms @{context} (map (JClause.term_of o snd) list_passive))
  val _ = writeln (Jeha_Common.pretty_terms @{context} (map JClause.term_of active))
  val _ = Jeha.given_clause_loop false (Config.put Jeha_Common.trace true (Jeha_Common.verbose_of ctxt)) 5 passive active (* handle TYPE (msg, _, ts) => error (msg ^ " " ^ (Jeha_Common.pretty_terms (verbose_of ctxt) ts)) *)
  val problem_term = @{term_pat "((bt_map (\<lambda>(a::bool). a) (Br ((?y1::?'a1::type) = ?y1) (?t1.0::bool bt) (?t2.0::bool bt))) = (Br True (bt_map (\<lambda>(a::bool). a) ?t1.0) (bt_map (\<lambda>(a::bool). a) ?t2.0)))"}
\<close>
*)






lemma bt_map_reflect: "bt_map f (reflect t) = reflect (bt_map f t)"
apply (induct t)
 apply (jeha bt_map.simps(1) reflect.simps(1))
by (jeha bt_map.simps(2) reflect.simps(2))






lemma preorder_bt_map: "preorder (bt_map f t) = map f (preorder t)"
apply (induct t)
 apply (jeha bt_map.simps(1) list.map(1) preorder.simps(1))
by simp

lemma inorder_bt_map: "inorder (bt_map f t) = map f (inorder t)"
proof (induct t)
  case Lf thus ?case
  proof -
    have "map f [] = []" by (jeha list.map(1))
    hence "map f [] = inorder Lf" by (jeha inorder.simps(1))
    hence "inorder (bt_map f Lf) = map f []" by (jeha bt_map.simps(1))
    thus "inorder (bt_map f Lf) = map f (inorder Lf)" by (jeha inorder.simps(1))
  qed
next
  case (Br a t1 t2) thus ?case by simp
qed

(* FIXME: requires EqHoist or clausifcation of \<leftrightarrow>
*)
lemma postorder_bt_map: "postorder (bt_map f t) = map f (postorder t)"
apply (induct t)
 apply (jeha Nil_is_map_conv bt_map.simps(1) postorder.simps(1))
by simp

lemma depth_bt_map [simp]: "depth (bt_map f t) = depth t"
apply (induct t)
 apply (jeha bt_map.simps(1) depth.simps(1))
by simp

lemma n_leaves_bt_map [simp]: "n_leaves (bt_map f t) = n_leaves t"
apply (induct t)
 apply (jeha bt_map.simps(1) n_leaves.simps(1))
proof -
  fix a :: 'b and t1 :: "'b bt" and t2 :: "'b bt"
  assume A1: "n_leaves (bt_map f t1) = n_leaves t1"
  assume A2: "n_leaves (bt_map f t2) = n_leaves t2"
  have "\<And>V U. n_leaves (Br U (bt_map f t1) V) = n_leaves t1 + n_leaves V"
    using A1 by (jeha n_leaves.simps(2))
  hence "\<And>V U. n_leaves (bt_map f (Br U t1 V)) = n_leaves t1 + n_leaves (bt_map f V)"
    by (jeha bt_map.simps(2))
  hence F1: "\<And>U. n_leaves (bt_map f (Br U t1 t2)) = n_leaves t1 + n_leaves t2"
    using A2 by jeha
  have "n_leaves t1 + n_leaves t2 = n_leaves (Br a t1 t2)"
    by (jeha n_leaves.simps(2))
  thus "n_leaves (bt_map f (Br a t1 t2)) = n_leaves (Br a t1 t2)"
    using F1 by jeha
qed

(* FIXME: requires EqHoist or clausifcation of \<leftrightarrow>
*)
lemma preorder_reflect: "preorder (reflect t) = rev (postorder t)"
apply (induct t)
 apply (jeha Nil_is_rev_conv postorder.simps(1) preorder.simps(1)
              reflect.simps(1))
apply simp
done

(* FIXME: requires EqHoist or clausifcation of \<leftrightarrow>
*)
lemma inorder_reflect: "inorder (reflect t) = rev (inorder t)"
apply (induct t)
 apply (jeha Nil_is_rev_conv inorder.simps(1) reflect.simps(1))
by simp
(* Slow:
by (metis append.simps(1) append_eq_append_conv2 inorder.simps(2)
          reflect.simps(2) rev.simps(2) rev_append)
*)

(*
ML \<open>
  val dumped_state = !Jeha_Tactic.dump;
  val (ctxt, countdown, passive, active) = nth dumped_state 0
  val _ = Jeha.given_clause_loop false (Jeha_Common.verbose_of ctxt) countdown passive active
\<close>
*)

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
  val clauses = map_index (fn (i, t) => JClause.of_term (t, i)) [@{term "x = y"}, @{term "y = z"}, @{term "x \<noteq> z"}]
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) (map JClause.term_of clauses))
  val result = Jeha.given_clause_loop false @{context} 12 (Jeha.init_passive_set clauses) []
\<close>

ML \<open>
  val f = @{term "f :: 'a \<Rightarrow> 'a"}
  val var_x = Var (("x", 0), @{typ "'a"})
  val f_is_id = HOLogic.mk_eq (f $ var_x, var_x)
  val clauses = map_index (fn (i, t) => JClause.of_term (t, i)) [f_is_id, @{term "f (f y) \<noteq> y"}]
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) (map JClause.term_of clauses))
  val result = Jeha.given_clause_loop false @{context} 10 (Jeha.init_passive_set clauses) []
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
  val clauses = map_index (fn (i, t) => JClause.of_term (t, i)) [zero_right_neutral, plus_def, two_neq_one_plus_one]
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) (map JClause.term_of clauses))
  (* FIXME: looks like some rewriting steps are missing pretty early on *)
  val result = Jeha.given_clause_loop false @{context} 40 (Jeha.init_passive_set clauses) []
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
  val clauses = map_index (fn (i, t) => JClause.of_term (t, i)) [eq, xxyz_neq_xy]
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) (map JClause.term_of clauses))
  val result = Jeha.given_clause_loop false @{context} 6 (Jeha.init_passive_set clauses) []
\<close>

(*
ML \<open>
  val c1 = @{term "P a :: bool"}
  val c2 = @{term "a = b"}
  val c3 = @{term "\<not> P b"}
  val clauses = map JClause.of_term [c1, c2, c3]
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) (map JClause.term_of clauses))
  val result = Jeha.given_clause_loop false @{context} 10 (Jeha.init_passive_set clauses) []
\<close>
*)

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





