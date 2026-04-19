theory delayed_unification

imports SLAM_TEST_BASE.test_base

begin

lemma "(\<And>x. P (x a)) \<Longrightarrow> (\<And>y. \<not> P (y b)) \<Longrightarrow> False"
  using [[
    slam_trace
  , slam_disable_all
  , slam_rule_flex_flex_simp
  , slam_rule_simp_outer_claus
  , slam_rule_sup
  , slam_rule_simp_false_elim
  ]] by slam

lemma "(\<And>x y. P (x a) (y b)) \<Longrightarrow> (\<And>u v. \<not> P (u c) (v d)) \<Longrightarrow> False"
  using [[
    slam_trace
  , slam_disable_all
  , slam_rule_flex_flex_simp
  , slam_rule_simp_outer_claus
  , slam_rule_sup
  , slam_rule_simp_false_elim
  ]] by slam

(* A higher-order Vampire, Example 1 *)
lemma "(\<And>x. x a b \<noteq> f b a \<or> x c d \<noteq> f b a) \<Longrightarrow> False"
  using [[slam_delayed_unification=false]] by slam

(* A higher-order Vampire, Example 1 *)
lemma "(\<And>x. x a b \<noteq> f b a \<or> x c d \<noteq> f b a) \<Longrightarrow> False"
  using [[slam_delayed_unification=true]] by slam

lemma "(\<And>x. x a b \<noteq> f b a \<or> x c d \<noteq> f b a) \<Longrightarrow> False"
using [[
    slam_trace,
    slam_disable_all,
    slam_rule_simp_outer_claus,
    slam_rule_e_res,
    slam_rule_sup,
    (* slightly closer to the example in the paper *)
    slam_literal_selection_function="select_first_neg_lit",
    slam_select_flex_sided,
    slam_delayed_unification=true,
    slam_unifier_cutoff=4 (* CRITICAL *)
  ]] by slam

ML_val \<open>
  val s_eq_t = @{term_schem "?x a b = f b a"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val ctxt = @{context} |> Config.put Unify.search_bound 1 (* has no effect *)
  val unifiers =
    Unify.unifiers
      ( (Context.Proof ctxt)
      , (Envir.empty 10)
      , [(s, t)]
      )
  val [uf1, uf2, uf3, uf4] = Seq.list_of (Seq.take 4 unifiers)
  fun pretty (unifier, ffs) =
    let
      val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
      val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
      val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
      val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)
    in
      (cs, ct, pretty_unifier, pretty_ffs, ics, ict)
    end
  val p1 = pretty uf1
  val p2 = pretty uf2
  val p3 = pretty uf3
  val p4 = pretty uf4
\<close>

(* A higher-order Vampire, Example 2 *)
lemma "f a = c \<Longrightarrow> (\<And>y. h (y b) (y a) \<noteq> h (g (f b)) (g c)) \<Longrightarrow> False"
using [[
    slam_trace
  , slam_disable_all
  , slam_rule_simp_outer_claus
  , slam_rule_sup
  , slam_rule_e_res
  , slam_delayed_unification=true
  , slam_rule_neg_cong_fun
  , slam_trace_e_res
  ]] by slam

declare [[slam_supress_unify_trace=false]]
declare [[slam_isabelle_unify_trace]]
declare [[slam_isabelle_unify_trace_bound=0]]
declare [[slam_isabelle_unify_trace_simp]]
declare [[unify_trace_failure]]

(* Our ERes with delayed unification doesn't work because it goes too deep. *)
ML_val \<open>
  val s_neq_t = @{term_schem "(h::'c \<Rightarrow> 'c \<Rightarrow> 'd) ((?y::'b \<Rightarrow> 'c) (b::'b)) (?y (a::'b)) \<noteq> h ((g::'a \<Rightarrow> 'c) ((f::'b \<Rightarrow> 'a) b)) (g (c::'a))"}
  val (s, t) = HOLogic.dest_eq (HOLogic.dest_not s_neq_t)
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val unifiers =
    Slam_Unify.preunifiers
      (Context.Proof @{context})
      [(s, t)]
      (Envir.empty 10)
  val u = Seq.pull unifiers
(*
  val (unifier, ffs) = Seq.hd unifiers
  val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
  val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
  val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
  val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)
*)
\<close>

declare [[slam_supress_unify_trace=true]]
declare [[slam_isabelle_unify_trace=false]]
declare [[slam_isabelle_unify_trace_bound=60]]
declare [[slam_isabelle_unify_trace_simp=false]]
declare [[unify_trace_failure=false]]

(* A modified NegCongFun can mimic ERes from the paper. (not a proper solution) *)
lemma "f a = c \<Longrightarrow> (\<And>y. h (y b) (y a) \<noteq> h (g (f b)) (g c)) \<Longrightarrow> False"
  using [[slam_delayed_unification=false, slam_neg_cong_fun_reveal_variable_headed]] by slam

lemma "f a = c \<Longrightarrow> (\<And>y. h (y b) (y a) \<noteq> h (g (f b)) (g c)) \<Longrightarrow> False"
  using [[slam_delayed_unification=true, slam_neg_cong_fun_reveal_variable_headed]] by slam

lemma "
      (\<And>z. z (f a) = (z :: 'a \<Rightarrow> 'd) c)
  \<Longrightarrow> (\<And>y. h (y b) (y a) \<noteq> h ((g :: 'a \<Rightarrow> 'd) (f b)) (g c))
  \<Longrightarrow> False
"
  using [[
      slam_delayed_unification=true
    , slam_disable_all
    , slam_rule_simp_outer_claus
    , slam_rule_sup
    , slam_sup_into_fluid
    , slam_sup_variable_condition="none"
    , slam_rule_e_res
    , slam_trace
    (* , slam_trace_sup *)
    , slam_max_number_of_steps=100
    , show_hyps
  ]] (* by slam (* FIXME: reconstruction failure *) *) sorry

declare [[show_hyps]]

ML_val \<open>
  val ctxt = @{context}
  val s_eq_t = @{term_schem "(?x :: 'a \<Rightarrow> 'a) a = (?y :: 'a \<Rightarrow> 'a) b"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val th = Slam_Proof_Util.refl_modulo_flex_flex ctxt (s, t)
  val th' =
    Thm.instantiate' [] [SOME (Thm.cterm_of ctxt @{term "\<lambda>x :: 'a. x"})] th

  val th2 = @{lemma "A \<Longrightarrow> A \<Longrightarrow> True" by auto}

  (* None of these leave the flex-flex pair alone*)
  val th3 = resolve_tac ctxt [th'] 1 th2 |> Seq.hd

  val th4 = compose_tac ctxt (false, th', 0) 1 th2 |> Seq.hd

  val th5 = Drule.comp_no_flatten (th', 0) 1 th2

  val th6 = th' COMP th2

  val th7 =
    Thm.bicompose
      (SOME ctxt)
      { flatten = false, incremented = false, match = false }
      (false, th', 0)
      1
      th2
    |> Seq.hd
\<close>

(* It doesn't just break the negative literal but arbitrary subterms. *)
ML_val \<open>
  val ctxt = @{context}
  val s_eq_t = @{term_schem "(?x :: 'a \<Rightarrow> 'a) a = (?y :: 'a \<Rightarrow> 'a) b"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val th = Slam_Proof_Util.refl_modulo_flex_flex ctxt (s, t)
  val th2 = mk @{term_schem "(?A :: bool) \<Longrightarrow> ?B \<Longrightarrow> ?A \<Longrightarrow> P ((?x :: 'a \<Rightarrow> 'a) a) \<Longrightarrow> True"}
  val th3 = compose_tac ctxt (false, th, 0) 1 th2 |> Seq.hd
  val th4 =
    Thm.instantiate' [] [SOME (Thm.cterm_of ctxt @{term "\<lambda>x :: 'a. x"})] th3
  val th5 = resolve_tac ctxt [@{lemma "True" by auto}] 1 th4 |> Seq.hd
\<close>

ML_val \<open>
  val ctxt = @{context}
  val s_eq_t = @{term_schem "(?x :: 'a \<Rightarrow> 'a) a = (?y :: 'a \<Rightarrow> 'a) b"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val th = Slam_Proof_Util.refl_modulo_flex_flex ctxt (s, t)
  val th2 = mk @{term_schem "(?A :: bool) \<Longrightarrow> ?B \<Longrightarrow> ?A \<Longrightarrow> P ((?x :: 'a \<Rightarrow> 'a) a) \<Longrightarrow> True"}
  val th3 = compose_tac ctxt (false, th, 0) 1 th2 |> Seq.hd
  val th4 =
    Thm.instantiate' [] [SOME (Thm.cterm_of ctxt @{term "\<lambda>x :: 'a. x"})] th3
  val th5 = resolve_tac ctxt [@{lemma "True" by auto}] 1 th4 |> Seq.hd
\<close>

(* Perhaps we can get rid of only the flex-flex pair in the thm but still keep it in the clause?

g (f a) \<noteq> ?z1 c \<Longrightarrow> ... \<Longrightarrow> False [g (f a) = ?z1 c]
---------------------------------------------------
g (f a) \<noteq> ?z1 c \<Longrightarrow> ... \<Longrightarrow> False []

When? Whenever we have that kind of reconstruction failure (maybe do something smarter later).

Currently:
* flex-flex pair in thm becomes rigid-flex
* the next resolution inference invokes the unification algorithm with this rigid-flex pair as one 
  of the disagreement pairs, solving it, and application of the unifier destroys the negative
  literal in the clause
* :(

Plan:

*)


(* New plan:

Find a way to move thm-attached flex-flex pairs into the prop.

This must somehow involve solving the flex-flex pairs for them to vanish.

C (?x a) (?y b) [?x a = ?y b]
----------------------------------------------------------------- (rename)
?x a = ?x' a \<Longrightarrow> ?y b = ?y' b \<Longrightarrow> C (?x' a) (?y' b) [?x a = ?y b]
----------------------------------------------------------------- (smash)
?h = ?x' a \<Longrightarrow> ?h = ?y' b \<Longrightarrow> C (?x' a) (?y' b) []
-------------------------------------------------- (??)
?x' a = ?y' b \<Longrightarrow> C (?x' a) (?y' b)

Possible solution:

generalize the "abstract_over" operation
* abstraction over arbitrary subterms

\<forall>x :: 'a. P x

\<lambda>t :: 'a \<Rightarrow> 'a. P (t x)

*)


ML\<open>
  val ctxt = @{context}
  val th =
    let
      val s_eq_t = @{term_schem "(?x :: 'a \<Rightarrow> 'a) a = (?y :: 'a \<Rightarrow> 'a) b"}
      val (s, t) = HOLogic.dest_eq s_eq_t
      val th_s_eq_t = Slam_Proof_Util.refl_modulo_flex_flex ctxt (s, t)
      val th_helper = mk @{term_schem "?A \<Longrightarrow> P ((?x :: 'a \<Rightarrow> 'a) a) ((?y :: 'a \<Rightarrow> 'a) b) \<noteq> Q \<Longrightarrow> False"}
    in
      compose_tac ctxt (false, th_s_eq_t, 0) 1 th_helper |> Seq.hd
      |> HClause.of_lemma
    end
(* ?x a \<rightarrow> ?xfresh a *)
(* ?x := \<lambda> ... ?xfresh ... *)
(* but instantiation also affect flex-flex pairs ... *)
(* So this won't work I guess? *)

(*
  This is rewriting, i.e. hard and bad.

  val th_x_eq_x_fresh =
    mk @{term_schem "(?x :: 'a \<Rightarrow> 'a) a = (?xfresh :: 'a \<Rightarrow> 'a) a \<Longrightarrow> ?x a \<noteq> ?xfresh a \<Longrightarrow> False"}
    |> HClause.of_lemma
  val th_x_renamed =
    Slam_Proof.reconstruct_sup ctxt
      { left_premise = th_x_eq_x_fresh
      , literal = (JLit.Left, 1)
      , right_premise = th
      , subterm = ([1], JLit.Left, 0)
      }
  val th_y_eq_y_fresh =
    mk @{term_schem "(?y :: 'a \<Rightarrow> 'a) b = (?yfresh :: 'a \<Rightarrow> 'a) b \<Longrightarrow> ?y b \<noteq> ?yfresh b \<Longrightarrow> False"}
    |> HClause.of_lemma
  val th_y_renamed =
    Slam_Proof.reconstruct_sup ctxt
      { left_premise = th_y_eq_y_fresh
      , literal = (JLit.Left, 1)
      , right_premise = th_x_renamed
      , subterm = ([2], JLit.Left, 1)
      }
*)
\<close>

find_theorems "?f \<equiv> ?g \<Longrightarrow> ?f ?x \<equiv> ?g ?x"

ML_val \<open>
  val ctxt = @{context}
  (* (\<lambda>u. ?x u) = (\<lambda>v. ?y v) \<Longrightarrow> \<lambda>w. P (?x w) = \<lambda>w. P (?y w) *)
  val lam_eq = mk @{term_schem "(\<lambda>u. ?x u a) \<equiv> (\<lambda>v. ?y v b)"}
  val ct = Thm.cterm_of ctxt @{term_schem "\<lambda>w. P (?x w a)"}
  fun beta_both lam_eq arg =
    let
      val app_eq_app = Drule.fun_cong_rule lam_eq arg
      val lhs = Thm.dest_arg1 (Thm.cprop_of app_eq_app)
      val (_, rhs) = Thm.dest_comb (Thm.cprop_of app_eq_app)
      val beta_lhs = Thm.symmetric (Thm.beta_conversion false lhs)
      val rhs_beta = Thm.beta_conversion false rhs
      val beta_beta = Thm.transitive beta_lhs (Thm.transitive app_eq_app rhs_beta)
    in
      beta_beta
    end
  val ff_lhs = Thm.dest_arg1 (Thm.cprop_of lam_eq)
  val (_, ff_rhs) = Thm.dest_comb (Thm.cprop_of lam_eq)
  val a = Conv.abs_conv (fn (cv, ctxt) => Conv.arg_conv (K (beta_both lam_eq cv))) ctxt ct
(* Normalization w.r.t. flex-flex pairs: *)
(* traverse term *)
(* Abs \<Rightarrow> abs_conv *)
(* variable-head \<Rightarrow> lookup matching flex-flex pair, rewrite *)

  fun resolve_flex_flex_disagreements ffpairs (s, t) =
    if s aconv t then Conv.all_conv else
    case (s, t) of
      (Var x, _) => error "" (* FIXME: lookup in ffpairs *)
    | (_ $ _, _) => if JTerm.is_variable_headed s then error "" else error ""
    | (Abs (x, sT, sb), Abs (y, tT, tb)) => error ""

  (* both as args \<rightarrow> produce a theorem *)
  (* (one as arg \<rightarrow> produce a theorem) = a conv *)
  (* Should conv's peak at the result? *)
\<close>

ML \<open>
  val s_eq_t = @{term_schem "h (?y b) (?y a) = h (g (f b)) (g c)"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val ctxt = @{context} |> Config.put Unify.search_bound 1 (* has no effect *)
  val unifiers =
    Unify.unifiers
      ( (Context.Proof ctxt)
      , (Envir.empty 10)
      , [(s, t)]
      )
  val ufs = Seq.list_of (Seq.take 4 unifiers)
  fun pretty (unifier, ffs) =
    let
      val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
      val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
      val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
      val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)
    in
      (cs, ct, pretty_unifier, pretty_ffs, ics, ict)
    end
(*
  val p1 = pretty uf1
  val p2 = pretty uf2
  val p3 = pretty uf3
  val p4 = pretty uf4
*)
\<close>

ML \<open>
  val s_eq_t = @{term_schem "(?z (f a)) = ?y a"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val ctxt = @{context} |> Config.put Unify.search_bound 1 (* has no effect *)
  val unifiers =
    Unify.unifiers
      ( (Context.Proof ctxt)
      , (Envir.empty 10)
      , [(s, t)]
      )
  val [uf1] = Seq.list_of (Seq.take 4 unifiers)
  fun pretty (unifier, ffs) =
    let
      val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
      val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
      val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
      val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)
    in
      (cs, ct, pretty_unifier, pretty_ffs, ics, ict)
    end
  val p1 = pretty uf1
(*
  val p2 = pretty uf2
  val p3 = pretty uf3
  val p4 = pretty uf4
*)
\<close>

ML \<open>
(*
  val D = mkh @{term_schem "(?y :: 'a \<Rightarrow> 'b) a \<noteq> b \<Longrightarrow> False"}
  val C = mkh @{term_schem "f ((?z :: 'a \<Rightarrow> 'b) c) = f b \<Longrightarrow> False"}
  val (t, t', true) = HClause.dest_lit_at 0 C
*)
(*

  D = ?x a = d
  C = f (?y b) \<noteq> f d
  
  unification yields

  \<sigma> = { ?x a \<mapsto> ?y b }

  apply preunifier to rewriting clause

  D' = ?x a \<noteq> ?y b \<or> f (?y a) = d

  ground superposition into C yields

  ?x a \<noteq> ?y b \<or> 
*)

(*

TODOS:

* Questions
  * How can flex-flex pairs arise?
    1. variable-headed subterms at equal subterm positions in a first-order-ish skeleton
    2. applying partial solution [?x = f (?y b)] yields situtation 1
      Example (see ML below):
        g ?x (f (?z a)) =\<^sup>? g (f (?y b)) ?x
  * Conjecture: If a preunifier contains a flex-flex pair involving ?x a then

* Proof Search

  * Normal form of flex-flex pairs.
    A flex-flex pair is in normal form if it is ordered with respect to 
    1. indexname_ord on the heads
    2. ? 

  * Normal form of sets of flex-flex pairs.
    * desideratum: every variable appears only one the left or only on the right
      problem: ?y a = ?y b
      solutions:
      1. introduce an auxialliary ?z variable and turn ?y a = ?y b into

  * Normal form of preunifiers.
    A preunifier ff \<union> \<sigma> is in normal form if
    * 

  * Three ways of applying a preunifier to a clause:
    1. apply the unifier, introduce flex-flex pairs as negative literals
    2. apply only the unifier (also applicable to terms)
    3. introduce only the flex-flex pairs as negative literals
    Note: all 3 are logically valid

* apply preunifer to clause
  * Scenario: t from D, u from C
    preunifier ff \<union> \<sigma>
    want to apply ff \<union> \<sigma> to D such that D(ff \<union> \<sigma>) contains
    t\<sigma> which is syntactically equal to u\<sigma>

    i.e. want all flex-flex constraints in the rewriting clause

  *
    C \<or> f (?x a) \<noteq> f (?y a)
    ------------------------ ERes
    C \<or> ?x a \<noteq> ?y a

  Alternative: introduce flex-flex literals into both clauses (i.e. simply when applying the
  unifier) and use LocalRw to rewrite everything else into a normal form.

*)

(*
  val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
  val unifiers =
    Slam_Unify.preunifiers
      (Context.Proof @{context})
      [(s, t)]
      (Envir.empty (HClause.maxidx_of C))
  val unifier = Seq.pull unifiers
*)
\<close>

ML_val \<open>
  val s_eq_t = @{term_schem "g ?x (f (?z a)) = g (f (?y b)) ?x"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val unifiers =
    Unify.unifiers
      ( (Context.Proof @{context})
      , (Envir.empty 10)
      , [(s, t)]
      )
  val (unifier, ffs) = Seq.hd unifiers
  val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
  val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
\<close>

ML_val \<open>
  (* Goal: single flex-flex pair where one of its sides does not occur in either instantiated term. *)
  (* This is not possible:
    1. for a variable to appear as a head in a flex-flex pair, there can't be an instantiation for
       that variable available
    2. 
  *)
  val s_eq_t = @{term_schem "g ?x (?x a) (?y c d) = g (\<lambda>x. ?z x b) (?y c) (?z a b d)"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val unifiers =
    Unify.unifiers
      ( (Context.Proof @{context})
      , (Envir.empty 10)
      , [(s, t)]
      )
  val (unifier, ffs) = Seq.hd unifiers
  val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
  val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
  val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
  val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)
\<close>

(*
?x a = ?y b

is there a most general assignment to ?x that satisfies this?

?x = \<lambda>z. t

?x a = t[a/z] != ?y b

*)

(*

Can flex-flex constraints be cyclic?

*)

(* flex-flex constraints are not normalized w.r.t. the substitution *)
ML_val \<open>
  val s_eq_t = @{term_schem "g (?x a) ?l = g (?l a) (\<lambda>a. ?y b)"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val unifiers =
    Unify.unifiers
      ( (Context.Proof @{context})
      , (Envir.empty 10)
      , [(s, t)]
      )
  val (unifier, ffs) = Seq.hd unifiers
  val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
  val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
  val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
  val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)
\<close>

(* normalizing flex-flex constraints with respect to the substitution helps *)
ML_val \<open>
  val s_eq_t = @{term_schem "g (?x a) ?l = g (?l a) (\<lambda>a. ?y b)"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val unifiers =
    Slam_Unify.preunifiers
      (Context.Proof @{context})
      [(s, t)]
      (Envir.empty 10)
  val (unifier, ffs) = Seq.hd unifiers
  val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
  val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
  val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
  val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)
\<close>

(* Can applying the substitution to a flex-flex pair make that pair unusable as a rewrite rule
because the pre-unified terms are not affected by the substitution in the same way? *)
(* ?x = \<lambda>u. ?y u a *)

(* flex-flex constraints can be solved by the substitution *)
(* but this might only happen in trivial cases such as \<sigma> = { ?x := ?l } below *)
ML_val \<open>
  val s_eq_t = @{term_schem "g (?x a) ?l = g (?l a) ?x"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val unifiers =
    Unify.unifiers
      ( (Context.Proof @{context})
      , (Envir.empty 10)
      , [(s, t)]
      )
  val (unifier, ffs) = Seq.hd unifiers
  val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
  val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
  val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
  val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)
\<close>

ML_val \<open>
  val s_eq_t = @{term_schem "g ?l (?x a b) (?y a b) = g (\<lambda>x. ?z x b) (?y a b) (?l (?x a))"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val unifiers =
    Unify.unifiers
      ( (Context.Proof @{context})
      , (Envir.empty 10)
      , [(s, t)]
      )
  val (unifier, ffs) = Seq.hd unifiers
  val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
  val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
  val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
  val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)
\<close>

(* flex-flex pairs can be lambdas *)
ML_val \<open>
  val s_eq_t = @{term_schem "(\<lambda>u. ?x u a) = (\<lambda>u. ?y u b)"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val unifiers =
    Unify.unifiers
      ( (Context.Proof @{context})
      , (Envir.empty 10)
      , [(s, t)]
      )
  val (unifier, ffs) = Seq.hd unifiers
  val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
  val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
  val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
  val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)
\<close>

(* The sides of flex-flex pairs aren't just always subterms of the preunified terms! *)
ML_val \<open>
  val s_eq_t = @{term_schem "(\<lambda>u. f (\<lambda>v. ?x v u a)) = (\<lambda>u. f (\<lambda>v. ?y u v b))"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val unifiers =
    Unify.unifiers
      ( (Context.Proof @{context})
      , (Envir.empty 10)
      , [(s, t)]
      )
  val (unifier, ffs) = Seq.hd unifiers
  val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
  val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
  val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
  val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)
\<close>

(* t =? t' *)

(* ?y a b = ?z c d   \<or> \<sigma> *)

(* ?y a b = ?z c d \<Longrightarrow> t\<sigma> = t'\<sigma> *)


(* Is it possible to work only with Isabelle's built-in handling of flex-flex pairs during proof
reconstruction? Or will we get "variable is free in assumptions" issues? *)

(* Idea: hthm's have flex-flex pairs attached to the theorem *and* as negative literals in the
clause. reconstruct_flex_flex_simp removes both the negative literals and discharges of the attached
flex-flex pairs *)

declare [[show_hyps]]

(*
* instantiate with preunifier
* resolve
* undo any renaming
*)

(* resolution without renaming *)
(* FIXME: What effect does protected have? *)
ML\<open>
  (* compare compose_tac *)
  fun compose ctxt th protected i =
    Thm.bicompose
      (SOME ctxt)
      {flatten = true, match = false, incremented = false}
      (false, th, protected)
      i
\<close>

ML_val\<open>
  val s_eq_t = @{term_schem "(\<lambda>z. f (?x z a)) = (\<lambda>z. f (?y z b))"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val unifiers =
    Unify.unifiers
      ( (Context.Proof @{context})
      , (Envir.empty 10)
      , [(s, t)]
      )
  val (unifier, ffs) = Seq.hd unifiers
  val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
  val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
  val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
  val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)

  val s_ceq_t = Thm.cterm_of @{context} s_eq_t
  val th1 = \<^instantiate>\<open>A = s_ceq_t in lemma\<open>A \<Longrightarrow> A\<close> by auto\<close>
  (* FIXME: check that INCR never misbehaves *)
  val th2 = @{thm HOL.refl} INCR_COMP th1
\<close>

(* reflexivity modulo flex-flex pairs *)

ML_val \<open>
  val s_eq_t = @{term_schem "(\<lambda>z. f (?x z a)) = (\<lambda>z. f (?y z b))"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val th = Slam_Proof_Util.refl_modulo_flex_flex @{context} (s, t)
\<close>

ML_val \<open>
  val s_eq_t = @{term_schem "(\<lambda>u. f (\<lambda>v. ?x u v a)) = (\<lambda>u. f (\<lambda>v. ?y u v b))"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val th' = Slam_Proof_Util.refl_modulo_flex_flex @{context} (s, t)
\<close>

ML_val \<open>
  val s_eq_t = @{term_schem "?x a = ?y b"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val th' = Slam_Proof_Util.refl_modulo_flex_flex @{context} (s, t)
\<close>

ML_val\<open>
  val s_eq_t = @{term_schem "a = b"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val () = \<^assert_cant>\<open>Slam_Proof_Util.refl_modulo_flex_flex @{context} (s, t)\<close>
\<close>

ML_val\<open>
  val s_eq_t = @{term_schem "?x = ?y"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val () = \<^assert_cant>\<open>Slam_Proof_Util.refl_modulo_flex_flex @{context} (s, t)\<close>
\<close>

ML_val\<open>
  val s_eq_t = @{term_schem "?x a = ?y"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val () = \<^assert_cant>\<open>Slam_Proof_Util.refl_modulo_flex_flex @{context} (s, t)\<close>
\<close>

ML_val\<open>
  val s_eq_t = @{term_schem "(\<lambda>u. f (?x u)) = (\<lambda>u. f (?y u))"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val th = Slam_Proof_Util.refl_modulo_flex_flex @{context} (s, t)
\<close>

(* New strategy:
  1. apply preunifier
  2. rewrite 
    2.1. build theorem t\<sigma> = u\<sigma> [.] using Slam_Proof_Util.refl_modulo_flex_flex
    2.2. 
  3. weaken by negative flex-flex literals
  4. some consistency check on the attached flex-flex pairs and the negative flex-flex literals?
*)

ML\<open>
  (* type disagreement = typ list * (term * term) *)
  type disagreement = JTerm.tpos
  (* we can build t = t' [.] *)
  val c = Conv.abs_conv (fn (v, ctxt) => fn ct => error "") @{context}
\<close>

ML\<open>
  val th = mk @{term_schem "A ?y \<Longrightarrow> P ((?y :: 'a \<Rightarrow> 'a) a)"}
  val th' = mk @{term_schem "P ((?x :: 'a \<Rightarrow> 'a) b) \<Longrightarrow> B ?x"}
  val th_res = resolve_tac @{context} [th] 1 th' |> Seq.hd
  val th_comp = compose_tac @{context} (false, th, 1) 1 th' |> Seq.hd
\<close>

ML\<open>
  val th = mk @{term "A \<Longrightarrow> B \<Longrightarrow> C"}
  val th' = mk @{term "(B \<Longrightarrow> C) \<Longrightarrow> D"}
  val th_comp = compose_tac @{context} (false, th, 1) 1 th' |> Seq.hd
  val th_comp_fail = compose_tac @{context} (false, th, 1) 2 th' |> Seq.hd
\<close>

(* What happens with flatten = false? *)
ML\<open>
  val th = mk @{term "A \<Longrightarrow> B \<Longrightarrow> C"}
  val th' = mk @{term "E \<Longrightarrow> C \<Longrightarrow> D"}
  val f =
    Thm.bicompose
      (SOME @{context})
      { flatten = false, match = false, incremented = false }
      (false, th, 2)
      2
      th'
    |> Seq.hd
\<close>

ML\<open>
  val th = mk @{term "A \<Longrightarrow> B \<Longrightarrow> C"}
  val th' = mk @{term "E \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> D"}
  val f =
    Thm.bicompose
      (SOME @{context})
      { flatten = false, match = false, incremented = false }
      (false, th, 1)
      2
      th'
    |> Seq.hd
\<close>

ML\<open>
  val th = mk @{term "A \<Longrightarrow> B \<Longrightarrow> (\<And>x. C x \<Longrightarrow> D x)"}
  val th_flat = Thm.cterm_of @{context} (Logic.flatten_params 0 (Thm.prop_of th))
  val th' = mk @{term "E \<Longrightarrow> (\<And>x. C x \<Longrightarrow> D x) \<Longrightarrow> F"}
  val f =
    Thm.bicompose
      (SOME @{context})
      { flatten = true, match = false, incremented = false }
      (false, th, 2)
      2
      th'
    |> Seq.hd
\<close>

ML\<open>
  val th = mk @{term "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D"}
  val th' = mk @{term "E \<Longrightarrow> (C \<Longrightarrow> D) \<Longrightarrow> F"}
  val th'' =
    (Thm.bicompose NONE {flatten = true, match = false, incremented = true}
        (false, th, 2) 2 th')
    |> Seq.hd
\<close>

ML\<open>
  val th = Skip_Proof.make_thm @{theory} @{term "\<And>x y. P x y \<Longrightarrow> Q"}
  val flat0 = Logic.flatten_params 0 (Thm.prop_of th) |> Thm.cterm_of @{context}
  val flat1 = Logic.flatten_params 1 (Thm.prop_of th) |> Thm.cterm_of @{context}
\<close>

ML\<open>
  val orule = mk @{prop "A"}
  val state = mk @{term "A \<Longrightarrow> R \<Longrightarrow> (\<And>x. Q x)"}
  val no_flatten =
    Thm.bicompose
      (SOME @{context})
      { flatten = false, match = false, incremented = false }
      (false, orule, 0)
      1
      state 
    |> Seq.hd
  val yes_flatten =
    Thm.bicompose
      (SOME @{context})
      { flatten = true, match = false, incremented = false }
      (false, orule, 0)
      1
      state
    |> Seq.hd
\<close>

ML\<open>
  val th = mk @{term "A \<Longrightarrow> B \<Longrightarrow> C"}
  val th' = mk @{term "(B \<Longrightarrow> C) \<Longrightarrow> D"}
  val th_comp = compose_tac @{context} (false, th, 1) 1 th' |> Seq.hd
\<close>

ML\<open>
  val th = mk @{term_schem "A ?x \<Longrightarrow> P ((?x :: 'a \<Rightarrow> 'a) a) (f ?y)"}
  val th' = mk @{term_schem "P ((?y :: 'a \<Rightarrow> 'a) b) (f ?x) \<Longrightarrow> B ?y"}
  val th'' = resolve_tac @{context} [th] 1 th' |> Seq.hd
\<close>

ML\<open>
  val th = mk @{term_schem "A ?x \<Longrightarrow> P ((?x :: 'a \<Rightarrow> 'a) a)"}
  val th' = mk @{term_schem "P ((?y :: 'a \<Rightarrow> 'a) b) \<Longrightarrow> B ?y"}
  val th'' = resolve_tac @{context} [th] 1 th' |> Seq.hd

  val s_eq_t = @{term_schem "f (?x :: 'a \<Rightarrow> 'a) (?y :: 'a \<Rightarrow> 'a) = f (\<lambda>x. a) (\<lambda>x. a)"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val unifiers =
    Unify.unifiers
      ( (Context.Proof @{context})
      , (Envir.empty 10)
      , [(s, t)]
      )
  val (unifier, ffs) = Seq.hd unifiers
  val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
  val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
  val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
  val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)

  val n = Thm.instantiate'
\<close>

(* There are "flex-flex pairs" of the form
  ?B = ?f ?B
which aren't really flex-flex pairs but are still returned as such (presumably because of the cyclic
dependency). *)
ML\<open>
  val s_eq_t = @{term_schem "summ (?h::?'b \<Rightarrow> ?'a) (?B::?'b set) = (?g::?'b \<Rightarrow> ?'a) ((jsk349 ::?'b set \<Rightarrow> (?'b \<Rightarrow> ?'a) \<Rightarrow> (?'b \<Rightarrow> ?'a) \<Rightarrow> ?'b) (?B::?'b set) ?g (?h::?'b \<Rightarrow> ?'a))"}
  val (s, t) = HOLogic.dest_eq s_eq_t
  val (pretty_s, pretty_t) = apply2 (Thm.cterm_of @{context}) (s, t)
  val unifiers =
    Unify.unifiers
      ( (Context.Proof @{context})
      , (Envir.empty 10)
      , [(s, t)]
      )
  val (unifier, ffs) = Seq.hd unifiers
  val (cs, ct) = apply2 (Thm.cterm_of @{context}) (s, t)
  val pretty_unifier = Slam_Common.pretty_env' @{context} unifier
  val pretty_ffs = map (apply2 (Thm.cterm_of @{context})) ffs
  val (ics, ict) = apply2 (Thm.cterm_of @{context} o Envir.norm_term unifier) (s, t)
\<close>

end