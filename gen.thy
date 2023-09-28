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
  HOL.Main
  SpecCheck.SpecCheck_Dynamic
  SpecCheck.SpecCheck_Generators
begin

ML_file \<open>jeha_common.ML\<close>
ML_file \<open>clause_id.ML\<close>
ML_file \<open>jterm.ML\<close>
ML_file \<open>jeha_order_reference.ML\<close>
ML_file \<open>jeha_order.ML\<close>
ML_file \<open>jlit.ML\<close>
ML_file \<open>jclause_pos.ML\<close>
ML_file \<open>jeha_log.ML\<close>
ML_file \<open>jclause.ML\<close>
ML_file \<open>jeha_proof.ML\<close>
ML_file \<open>jeha_unify.ML\<close>

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
  (* probability of generating a constant *)
  val prob_of_constant = (* 0.3 *) 0.0
  (* Precomputed, from the paper, presumably increasing the probability of
  boltzmann_index leads to smaller terms. Weaker effect when increasing the
  probability of boltzmann_lambda. *)
  (* Scale precomputed values into interval determined by 1 - prob_of_constant. *)
  fun rescale r = (1.0 - prob_of_constant) * r + prob_of_constant
  fun boltzmann_constant r = r < prob_of_constant
  fun boltzmann_index r = r < rescale 0.35700035696434995;
  fun boltzmann_lambda r = r < rescale (* 0.6 *) 0.6525813160382378;
  (* The probability p of de Bruijn index 0, generally Bound j has the
  probability (1-p)^j * p (geometric distribution) *)
  fun boltzmann_leaf r = r < rescale (* 0.65 *) 0.7044190409261122;
\<close>

ML_file \<open>jeha_gen_term.ML\<close>

ML \<open>
  (* (rng state, env, maxidx) *)
  type term_state = SpecCheck_Random.rand * Type.tyenv * int;

  fun pick_index _ [] _ _ = error "pick_index: not below lambda"
    | pick_index (ctxt : Proof.context) (T::Ts) typ (s, env) =
    let
      val (r, s) = SpecCheck_Generator.range_real (0.0, 1.0) s
    in
      if boltzmann_leaf r
        then ((s, Sign.typ_unify (Proof_Context.theory_of ctxt) (T, typ) env), Bound 0)
        else
          let val (state, Bound i) = pick_index ctxt Ts typ (s, env) in
            (state, Bound (i+1))
          end
    end;

  fun gen_fresh_tyvar ctxt maxidx =
    (maxidx + 1, TVar ((Name.aT, maxidx + 1), Sign.defaultS (Proof_Context.theory_of ctxt)));
  
  fun ran_constant ctxt typ (s, (typ_env, maxidx)) =
    let
      fun upshift_TVar j (TVar ((name, i), T)) = TVar ((name, i + j), T)
        | upshift_TVar _ T = T
      fun map_const f (t as (Const _)) = f t
        | map_const _ t = t
      val freshen_type = map_const (map_types (map_atyps (upshift_TVar maxidx)))
      val constants =
        ctxt
        |> Proof_Context.theory_of
        |> Sign.consts_of
        |> Consts.dest
        |> #constants
        (* discard Pure... constants, length of 11 is a good cutoff that includes HOL.False *)
        |> filter (fn (name, _) => String.isPrefix "HOL" name andalso String.size name <= 11)
        (* |> filter (fn (name, _) => String.isPrefix "HOL.All" name orelse String.isPrefix "HOL.False" name) *)
        |> map (fn (name, (T, _)) => Const (name, T))
        (* |> curry (op @) [Free ("c", TVar (("'a", 0), [])), Free ("d", TVar (("'b", 0), []))] *)
      val (constant, s) = SpecCheck_Generator.elementsL constants s
      val constant = freshen_type constant
      val T = fastype_of constant
      val maxidx = Term.maxidx_typ T maxidx
      val (typ_env, maxidx) =
        Sign.typ_unify
          (Proof_Context.theory_of ctxt)
          (T, typ)
          (typ_env, maxidx)
    in
      ((s, (typ_env, maxidx)), constant)
    end

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

    (* let
      val (r, s) = SpecCheck_Generator.range_real (0.0, 1.0) s
    in
      if boltzmann_constant r
        then ran_constant ctxt typ (s, (typ_env, maxidx))
      else if boltzmann_index r
        then pick_index ctxt binder_types typ (s, (typ_env, maxidx))
      else if boltzmann_lambda r
        then
          let
            val (maxidx, arg_T) = gen_fresh_tyvar ctxt maxidx
            val (maxidx, return_T) = gen_fresh_tyvar ctxt maxidx
            (* The type of the thing we're generating. *)
            val lambda_typ = arg_T --> return_T
            (* The `typ` we were asked to return must unify the type we're
            actually generating *)
            val (typ_env, maxidx) =
              Sign.typ_unify
                (Proof_Context.theory_of ctxt)
                (lambda_typ, typ)
                (typ_env, maxidx)
            val (state, body) =
              ran_typable
                ctxt
                (arg_T :: binder_types)
                return_T
                (s, (typ_env, maxidx))
          in
            (state, Abs (Name.uu_, arg_T, body))
          end
      else
        let
          val (maxidx, arg_T) = gen_fresh_tyvar ctxt maxidx
          val (state, function) =
            ran_typable ctxt binder_types (arg_T --> typ) (s, (typ_env, maxidx))
          val (state, arg) =
            ran_typable ctxt binder_types arg_T state
        in
          (state, function $ arg)
        end
    end *)

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

(* declare [[show_types]] *)

ML \<open>
  val check_term = SpecCheck.check (SpecCheck_Show.term @{context}) boltzmann_term_gen
  (* val check_term = SpecCheck.check (SpecCheck_Show.term @{context}) (boltzmann_term_gen_min_size 5) *)
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
