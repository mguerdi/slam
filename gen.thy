(*

Random generator for lambda expressions. Based on the paper

  Maciej Bendkowski, Katarzyna Grygiel and Paul Tarau. “Random generation of
  closed simply typed \<lambda>-terms: A synergy between logic programming and
  Boltzmann samplers”

with parts taken from
  https://github.com/kappelmann/ml-unification-isabelle/blob/e6041fab99ff29c7e763923cdea4d3de59b6a037/Tests/tests_base.ML

*)

theory gen
imports
  "tests/test_base"
  SpecCheck.SpecCheck_Dynamic
  SpecCheck.SpecCheck_Generators
begin

ML_file \<open>jeha_gen_term.ML\<close>

ML \<open>
  fun gen_fresh_tyvar ctxt maxidx = (* Jeha_Gen_Term.fresh_tvar () *)
    (maxidx + 1, TVar ((Name.aT, maxidx + 1), Sign.defaultS (Proof_Context.theory_of ctxt)));
  
  (* Generate a typable, closed random term. Rejection sampler with early abort
  that fails via exceptions. *)
  fun ran_typable
        (ctxt : Proof.context)
        (binder_types : typ list)
        (typ : typ)
        ((s, (typ_env, maxidx)) : SpecCheck_Random.rand * (Type.tyenv * int))
        : (SpecCheck_Random.rand * (Type.tyenv * int)) * term =
    let
      val (t, ((_, typ_env, maxidx), s)) =
        Jeha_Gen_Term.term binder_types typ ((ctxt, typ_env, maxidx), s)
    in
      ((s, (typ_env, maxidx)), t)
    end

  type boltzmann_config =
    { T : typ, free_names : string list, const_names : string list, min_size : int }

  fun boltzmann_term_of_type_failing_gen (T : typ) : (term, SpecCheck_Random.rand) SpecCheck_Generator.gen_state = fn s =>
    let
      val maxidx = Term.maxidx_of_typ T
      val ((s, (typ_env, maxidx)), t) =
        ran_typable @{context} [] T (s, (Vartab.empty, maxidx))
      val t =
        Envir.norm_term
          (Envir.Envir {maxidx = maxidx, tenv = Vartab.empty, tyenv = typ_env})
          t
    in
      (t, s)
    end

  val boltzmann_term_failing_gen =
    boltzmann_term_of_type_failing_gen (snd (gen_fresh_tyvar @{context} 1))

  (* rejection sampling *)
  fun retry_on_exception_gen gen s =
    let
      val s = SpecCheck_Random.next s
    in
      gen s
        handle _ => retry_on_exception_gen gen s
    end

  val boltzmann_term_gen = retry_on_exception_gen boltzmann_term_failing_gen

  fun min_size_gen min_size gen =
    SpecCheck_Generator.filter
      (fn t => size_of_term t >= min_size)
      gen

  fun boltzmann_term_gen_min_size min_size
    = min_size_gen min_size boltzmann_term_gen
  
  fun boltzmann_term_of_type_gen T = retry_on_exception_gen (boltzmann_term_of_type_failing_gen T)

\<close>

declare [[speccheck_num_counterexamples = 100]]
declare [[speccheck_max_success = 100]]

declare [[show_types]]

ML \<open>
  (* val check_term = SpecCheck.check (SpecCheck_Show.term @{context}) boltzmann_term_gen *)
  val check_term = SpecCheck.check (SpecCheck_Show.term @{context}) (boltzmann_term_gen_min_size 12)
  (* val check_term =
    SpecCheck.check
      (SpecCheck_Show.term @{context})
      (
        SpecCheck_Generator.map
          (fn t => JTerm.ensure_lambda_under_q (HOLogic.all_const (body_type (fastype_of t)) $ t))
          (min_size_gen 5 (boltzmann_term_of_type_gen @{typ_pat "(?'a => bool)"}))
      ) *)
  val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
  val _ = Lecker.test_group ctxt (SpecCheck_Random.new ()) [
    SpecCheck_Property.prop (K false) (* (is_some o try (Syntax.check_term ctxt)) *)
    |> check_term "boltzmann generator type checks"
  ]
\<close>

ML_val \<open>
  (* val example_term = @{term_schem "?x3 (\<lambda>x xa xb xc xd. xb (xd (\<lambda>x xa. xa (?x24 x))) x (xa (?x32 (xd xc)) xd xb))"} *)
  val example_term = @{term_schem "?x3 (\<lambda>x. x (x (\<lambda>x. x) (\<lambda>x xa. ?x16)) (?x18 (x (\<lambda>x xa. ?x24))))"}
  val example_term = @{term_schem "?x3 (\<lambda>x xa. xa ?x10 (\<lambda>x. ?x18 ?x22 x (\<lambda>x xa. ?x29) x ?x30))"}
  val example_term = @{term_schem "?x4 (\<lambda>x xa. xa (xa (\<lambda>x xa xb. x (\<lambda>x xa. x))) (?x25 x) x) (\<lambda>x. ?x28)"}
  val vars = Term.add_vars example_term []
  val bla = map (writeln o Jeha_Common.pretty_term (Jeha_Common.verbose_of @{context}) o Var) vars;
  val _ = writeln (Jeha_Common.pretty_term (Jeha_Common.verbose_of @{context}) example_term);
\<close>

ML \<open>
  val t = @{term_schem "\<lambda>uu. ?x9 (\<lambda>z. uu) (\<lambda>uua . uua (\<lambda>uua . ?x26 (?x28 (?x30 (uua (uua uu (?x35 (?x38 (\<lambda>uu. uu) uua)))))) (?x30 (uua (uua uu (?x35 (?x38 (\<lambda>uu. uu) uua)))))))"}

  (* val vs = subst_Vars [(("x", 26), ] t  *)
\<close>

declare [[speccheck_num_counterexamples = 10]]
declare [[speccheck_max_success = 10]]

(* ML \<open>
  fun show_termpair ctxt =
    let val pretty_term = Syntax.pretty_term ctxt
    in SpecCheck_Show.zip pretty_term pretty_term end
  val term_gen = boltzmann_term_gen_min_size 3
  val boltzmann_term_pair_gen = SpecCheck_Generator.zip term_gen term_gen
  val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
  val check_kbo = SpecCheck.check (show_termpair ctxt) boltzmann_term_pair_gen
  (* print some unifiable terms lambda expressions *)
  val _ = Lecker.test_group ctxt (SpecCheck_Random.new ()) [
    SpecCheck_Property.prop (fn term_pair => (is_none o Seq.pull) ( Jeha_Unify.smash_unifiers (Context.Proof ctxt) [term_pair] Envir.init)) |> check_kbo "kbo"
  ]

  (* val smash_unifiers: Context.generic -> (term * term) list -> Envir.env -> Envir.env Seq.seq *)
\<close>

declare [[show_types, show_sorts]]

ML \<open>
  val c = Sign.consts_of @{theory} |> Consts.dest |> #constraints;
  val cs =
    Sign.consts_of @{theory} |> Consts.dest |> #constants
    |> filter (fn (name, _) => String.isPrefix "HOL" name andalso String.size name <= 11);
  val pretty_cs =
    cs
    |> map (fn (name, (T, t)) =>
        Pretty.block ([
          Pretty.str (name ^ " : "),
          Syntax.pretty_typ @{context} T
        ]
        @
        (case t of
          SOME t =>
            [
              Pretty.str "            (",
              Syntax.pretty_term @{context} t,
              Pretty.str ")"
            ]
        | NONE => []))
        )
    |> Pretty.enum "\n" "[" "]"
\<close> *)

end
