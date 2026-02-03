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

end