theory jeha_test

imports "tests/test_base" Main HOL.Hilbert_Choice

begin

notation (output) "Pure.prop" ("#_" [1000] 1000)

ML \<open>
  ML_system_pp (fn _ => fn _ => Pretty.to_polyml o Jeha_Common.raw_pp_typ);
  ML_system_pp (fn _ => fn _ => Pretty.to_polyml o Jeha_Common.raw_pp_term);
  (* reset to default pretty printer *)
  ML_system_pp (fn depth => fn _ => ML_Pretty.to_polyml o Pretty.to_ML depth o Proof_Display.pp_typ Theory.get_pure);
  ML_system_pp (fn depth => fn _ => ML_Pretty.to_polyml o Pretty.to_ML depth o Proof_Display.pp_term Theory.get_pure);
\<close>

declare [[ML_debugger = true]]
declare [[ML_exception_trace = true]]
declare [[ML_exception_debugger = true]]

declare [[jeha_trace = true]]

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
      "term:\t\t" ^ Jeha_Common.pretty_term ctxt term ^ "\ngreens:\t\t" ^ Jeha_Common.pretty_terms ctxt green_subterms ^
      "\nnongreens:\t" ^ Jeha_Common.pretty_terms @{context} non_green_subterms
    end;
  writeln (pretty_green_nongreen_subterms @{context} @{term_pat "f (g (\<not> p)) (\<forall> x . q) (?y a) (\<lambda> x . h b)"});
  fun pretty_normed_unnormed ctxt term =
    let val normed = JTerm.norm_quantifier_poly_eq term in
    "Q\<^sub>\<approx>: " ^ Jeha_Common.pretty_term ctxt term ^ "  \<mapsto>  " ^ Jeha_Common.pretty_term ctxt normed end;
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
  writeln (Jeha_Common.pretty_term @{context} (HOLogic.mk_not (HOLogic.mk_eq (@{term "a::'a"}, @{term "b::'a"}))));
\<close>

(* sup tests *)
ML \<open>
  (* part of Example 25 from o\<lambda>Sup paper (WORKS) *)
  val (a, b, w) = (@{term "a::'a"}, @{term "b::'a"}, @{term_pat "?w::'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"});
  val cs = Jeha.infer_sup @{context} (JClause.of_literals ([(w $ a $ b $ b, w $ b $ a $ b, true)], 0), (JLit.Left, 0)) (JClause.of_literals ([(a, b, false)], 1), ([], JLit.Right, 0));
  writeln (Jeha_Common.pretty_terms @{context} (map JClause.term_of cs));
  (* part of Example 27 from the o\<lambda>Sup paper (WORKS) *)
  val (a, b, h, g) = (@{term "a::'a"}, @{term "b::'a"}, @{term "h::'b \<Rightarrow> 'c"}, @{term "g::bool \<Rightarrow> 'c"})
  val (x2, x3) = (@{term_pat "?x2 :: 'a \<Rightarrow> 'd"}, @{term_pat "?x3 :: 'a \<Rightarrow> 'd"});
  (* val d = [((h $ (g $ (HOLogic.mk_eq (x2 $ a, x3 $ a)))), h $ (g $ @{term True}), false), (@{term False}, @{term True}, true), (x2 $ b, x3 $ b, true)];
  val d_term = Jeha.term_of_clause d; *)
  val d = JClause.of_term (@{term_pat "h(g(?x2 a = ?x3 a)) \<noteq> h(g(True)) \<or> False = True \<or> ?x2 b = ?x3 b"}, 2);
  (* writeln ("D_anti: " ^ Jeha_Common.pretty_term @{context} d_anti);
  writeln ("D_anti_clause: " ^ Jeha_Common.pretty_term @{context} (JClause.term_of (JClause.of_term d_anti))); *)
  writeln ("D: " ^ Jeha_Common.pretty_term @{context} (JClause.term_of d));
  val c = JClause.of_literals ([(a, b, false)], 3);
  writeln ("C: " ^ Jeha_Common.pretty_term @{context} (JClause.term_of c));
  val cs = Jeha.infer_sup @{context} (d, (JLit.Left, 2)) (c, ([], JLit.Right, 0));
  val cs_terms = map JClause.term_of cs;
  writeln (Jeha_Common.pretty_terms @{context} (map JClause.term_of cs));
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
      Jeha_Common.pretty_term ctxt' (Thm.prop_of thm)
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

(* BoolRw bug? *)
ML_val \<open>
val c = JClause.of_term (@{term_pat "False = True \<or> (f ?x = f ?x) = True"}, 0)
val [inferred] = Jeha.infer_bool_rw @{context} c ([], JLit.Left, 1)
(* this is wrong: *)
val ctxt = Config.map Jeha_Common.disable_all (K true) @{context}
(* val ctxt = ctxt |> fold (fn rule => Config.map rule (K true)) [Jeha_Common.rule_delete_duplicated_lits] *)
val cheap_simplified = Jeha.forward_simplify ctxt true [] inferred
(* this is okay: *)
val resolved_lits_deleted = Jeha.simp_delete_resolved_lits @{context} inferred
val duplicated_lits_deleted = Jeha.simp_delete_duplicated_lits @{context} inferred
val [tf, tt] = JClause.literals inferred
val tf_tt_aconv = JLit.aconv (tf, tt) 
val tt_tf_aconv = JLit.aconv (tt, tf)
val cposs_of_dups =
  fold_index
    (fn (i, l) => fn (dup_is, head_list) =>
      if exists (curry JLit.aconv l) head_list
        (* duplicate of l has already been seen *)
        then (i::dup_is, head_list)
        (* l is new, add it to the seen lits *)
        else (dup_is, l::head_list))
    (* (JClause.literals inferred) *)
    [tf, tt]
    ([], [])
\<close>

ML \<open>
  (* val false_refl_clause = JClause.of_term (@{term "False = False"}, 0) *)
  (* SOME z . \<not> (y z) *)
  (* val offending_term = @{term_pat "(SOME (z::?'b1). (\<not> ((?y1::(?'b1 \<Rightarrow> bool)) z))) = False"} *)
  val offending_term = @{term "((SOME (z::('a \<Rightarrow> bool)). (\<forall>(x::'a). ((z x) = (((p::('a \<Rightarrow> bool)) x) \<and> ((q::('a \<Rightarrow> bool)) x))))) = True)"}
  val arg_congs = Jeha.infer_arg_cong @{context} false_refl_clause 0
\<close>

(*
ML \<open>
  fun my_of_list xs = fold (fn x => fn acc => Seq.cons x acc) xs Seq.empty 
  fun lazy_of_list [] = Seq.empty
    | lazy_of_list (x :: xs) = Seq.make (fn _ => SOME (x, lazy_of_list xs))
  fun lazy_prefix_map x ys = Seq.map (pair x) ys
  fun lazy_cart xs ys =
    Seq.make (fn () =>
      case Seq.pull xs of
        SOME (x, xs) => Seq.pull (Seq.append (lazy_prefix_map x ys) (lazy_cart xs ys))
      | NONE => NONE
    )
\<close>

ML \<open>
  val long_list = replicate 30000000 5
  (* val long_list = replicate 30000 5 *)
  fun writeln_seq s 0 = Seq.empty 
    | writeln_seq s n = Seq.make (fn _ => SOME (writeln s, writeln_seq s (n-1)))
\<close>

ML \<open>
  val long_seq = lazy_of_list long_list
  val hello_seq_5 = writeln_seq "hello" 5
  val bye_seq_5 = writeln_seq "bye" 5
\<close>

ML \<open>
  val cart = lazy_cart long_seq long_seq
  val hello_bye_cart = lazy_cart hello_seq_5 bye_seq_5
  val it = Seq.pull long_seq
  val SOME (_, hb_tl) = Seq.pull hello_bye_cart
  val _ = Seq.pull hb_tl
\<close>
*)

(*
ML \<open>
  val dumped_state = !Jeha_Tactic.dump;
  val dumped_states = length dumped_state;
  val { context = context, countdown = countdown, passive = passive, active = active, archive = archive } = nth dumped_state 0
  val state = { context = Jeha_Common.verbose_of context, countdown = 1, passive = passive, active = active, archive = archive }
  val (given_clause, passive) = Jeha.select_given_clause passive
  val [simplification] = Jeha.forward_simplify context false active given_clause
  val same = (JClause.literals simplification = JClause.literals given_clause)
  val (redundant_active, simplified_active, unsimplifiable_active) =
    Jeha.backward_simplify context active given_clause
  (* val _ = Jeha.given_clause_loop false state (* handle TYPE (msg, _, ts) => error (msg ^ " " ^ (Jeha_Common.pretty_terms (Jeha_Common.verbose_of ctxt) ts)) *) *)
  val active = given_clause :: unsimplifiable_active
  val inferred_clauses = Jeha.infer_clauses context active given_clause
  val bad_clause = nth inferred_clauses 3
  val _ = writeln ("Bad: " ^ JClause.pretty_clause context bad_clause)
  val second_bad_clause = nth inferred_clauses 4
  val _ = writeln ("Also bad: " ^ JClause.pretty_clause context second_bad_clause)
  
  val _ = writeln ("Number of passive clauses: " ^ @{make_string} (length (Seq.list_of (Jeha.seq_of_passive_set passive))))

  val context = Config.put Jeha_Common.disable_all true context
  (* val context =
    context
    |> fold (fn rule => Config rule true [
    ] *)
  val _ = writeln "cheap simplify test"
  val c = JClause.of_term (@{term_pat "p (SOME z. ?x4 z \<noteq> (p z \<and> q z)) = True \<or> q (SOME z. ?x4 z \<noteq> (p z \<and> q z)) = True \<or> (?x4 (SOME z. ?x4 z \<noteq> (p z \<and> q z)) = (False \<and> False)) = False"}, 0)
  val d = JClause.of_term (@{term_pat "(False \<and> False) = True \<or> p (SOME z. ?x z \<noteq> (p z \<and> q z)) = True \<or> q (SOME z. ?x z \<noteq> (p z \<and> q z)) = True \<or> (?x (SOME z. ?x z \<noteq> (p z \<and> q z)) = False) = False"}, 1)
  val c_subs_d = Jeha_Subsumption.subsumes (Context.Proof context) (c, d)

  (* val bad_matchers = Jeha_Unify.literal_matchers (Context.Proof context) 5 (nth (JClause.literals c) 2, nth (JClause.literals d) 4)
  val bad_matcher = Seq.pull bad_matchers *)

  (* val is_redundant = Jeha.is_redundant context active bad_clause *)
  (* val subs = exists (fn ac => Jeha_Subsumption.subsumes (Context.Proof context) (ac, bad_clause)) active *)
  (* val eq_subs = exists (fn ac => Jeha.equality_subsumes context (ac, bad_clause) orelse Jeha_Subsumption.subsumes (Context.Proof context) (ac, c)) active
  val is_trivial = Jeha.is_trivial bad_clause  *)
  (* val simplified = Jeha.forward_simplify context true active (nth inferred_clauses 3) *)




  fun f g 0 = g ()
    | f g n = f g (n-1)
  (* val _ = f (fn () => writeln "deep") 8070000 *)
\<close>
*)

(*
(* FIXME: BoolRw is not applicable... Is Outer clausification necessary for completeness? *)
lemma test2:
  shows "(x = y) \<Longrightarrow> (y = z) \<longrightarrow> (x = z)"
  by jeha

(* FIXME: BoolRw is not applicable... Is Outer clausification necessary for completeness? *)
lemma test3:
  shows "(A \<Longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B"
  by jeha
*)

declare [[show_types]]
ML \<open>
  val t = @{term_pat "?y :: ?'a \<Rightarrow> bool"}
  val fa_a = HOLogic.all_const @{typ_pat "?'a"} $ t
  val T = type_of fa_a
  val normed = JTerm.ensure_lambda_under_q fa_a
\<close>

(*
ML \<open>
  val dumped_state = !Jeha_Tactic.dump;
  val dumped_states = length dumped_state;
  val { context = context, countdown = countdown, passive = passive, active = active, archive = archive } = nth dumped_state 0
  val state = { context = Jeha_Common.verbose_of context, countdown = countdown, passive = passive, active = active, archive = archive }
  val _ = Jeha.given_clause_loop false state (* handle TYPE (msg, _, ts) => error (msg ^ " " ^ (Jeha_Common.pretty_terms (Jeha_Common.verbose_of ctxt) ts)) *)
\<close>
*)

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
  val _ = Jeha.given_clause_loop false (Config.put Jeha_Common.trace true ctxt) 5 passive active (* handle TYPE (msg, _, ts) => error (msg ^ " " ^ (Jeha_Common.pretty_terms (Jeha_Common.verbose_of ctxt) ts)) *)
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
  val _ = writeln ("NUMBER OF DUMEPD STATES = " ^ @{make_string} dumped_states)
  val (ctxt, countdown, passive, active) = nth dumped_state 0
  fun seq_of_passive_set passive =
    if Jeha.Passive_Set.is_empty passive
      then Seq.empty
      else Jeha.Passive_Set.min_elem passive ||> seq_of_passive_set |> uncurry Seq.cons
  val list_passive = Seq.list_of (seq_of_passive_set passive)
  val _ = writeln (Jeha_Common.pretty_terms @{context} (map (JClause.term_of o snd) list_passive))
  val _ = writeln (Jeha_Common.pretty_terms @{context} (map JClause.term_of active))
  val _ = Jeha.given_clause_loop false (Config.put Jeha_Common.trace true (Jeha_Common.verbose_of ctxt)) 5 passive active (* handle TYPE (msg, _, ts) => error (msg ^ " " ^ (Jeha_Common.pretty_terms (Jeha_Common.verbose_of ctxt) ts)) *)
  val problem_term = @{term_pat "((bt_map (\<lambda>(a::bool). a) (Br ((?y1::?'a1::type) = ?y1) (?t1.0::bool bt) (?t2.0::bool bt))) = (Br True (bt_map (\<lambda>(a::bool). a) ?t1.0) (bt_map (\<lambda>(a::bool). a) ?t2.0)))"}
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
  val result = Jeha.given_clause_loop false { context = @{context}, countdown = 12, passive = (Jeha.init_passive_set clauses), active = [], archive = [] }
\<close>

ML \<open>
  val f = @{term "f :: 'a \<Rightarrow> 'a"}
  val var_x = Var (("x", 0), @{typ "'a"})
  val f_is_id = HOLogic.mk_eq (f $ var_x, var_x)
  val clauses = map_index (fn (i, t) => JClause.of_term (t, i)) [f_is_id, @{term "f (f y) \<noteq> y"}]
  val _ = writeln (Jeha_Common.pretty_terms (Jeha_Common.verbose_of @{context}) (map JClause.term_of clauses))
  val result = Jeha.given_clause_loop false { context = @{context}, countdown = 10, passive = (Jeha.init_passive_set clauses), active = [], archive = [] }
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
  val result = Jeha.given_clause_loop false { context = @{context}, countdown = 40, passive = (Jeha.init_passive_set clauses), active = [], archive = [] }
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
  val result = Jeha.given_clause_loop false { context = @{context}, countdown = 6, passive = (Jeha.init_passive_set clauses), active = [], archive = [] }
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

