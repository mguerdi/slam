(*

general procedure:

1. Q\<^sub>\<approx> normalize
2. \<beta>\<eta>Q\<^sub>\<eta>-normalize
3. 

*)

signature SLAM =
sig
  type clause_lit = JClause.T * JClause.cpos * JClause.eligibility
  type clause_lit_side = JClause.T * (JLit.lpos * JClause.cpos) * JClause.eligibility
  type clause_term = JClause.T * JClause.full_pos * JClause.eligibility
  type unit_clause = JClause.T * JLit.lpos * JClause.eligibility

  val impl_simp_rewrite_lits : Proof.context -> unit_clause -> clause_term -> JClause.T option
  val find_single_green_disagreement : Proof.context -> term * term -> JTerm.tpos option
  val literal_can_match_single_disagreement : Proof.context -> int * JLit.T -> int * JLit.T -> (int * (JTerm.tpos * (JLit.lpos * Envir.env))) option
  val equality_subsumes : Proof.context -> JClause.T * JClause.T -> bool
  val bool_rw_non_var_rules : bool -> (term * term) list
  (* outer clausification *)
  val outer_clausify :
    Proof.context
    -> int
    -> bool
    -> term
    -> JClause.T
    -> (JClause.T * (term * (term, (term * term * term)) Slam_Common.either) option) list
             (*        ^       ^             ^          *)
             (*   predicate variable      skolem        *)
  val is_trivial : JClause.T -> bool
  val is_equality_subsumed : Proof.context -> Slam_Clause_Set.T -> JClause.T -> bool
  val simp_bool_outer_claus : Proof.context -> clause_lit -> JClause.T list
  val simp_rewrite_lits : Proof.context -> unit_clause -> clause_term -> JClause.T option
  val simp_delete_resolved_lits : Proof.context -> JClause.T -> JClause.T option
  val simp_delete_duplicated_lits : Proof.context -> JClause.T -> JClause.T option
  (* val simp_bool_rw : Proof.context -> clause_term -> JClause.T list *)
  val infer_eq_neq_outer_claus : Proof.context -> clause_lit -> JClause.T list
  val infer_sup : Proof.context -> clause_lit_side -> clause_term -> JClause.T list
  val infer_eres : Proof.context -> clause_lit -> JClause.T list
  val infer_efact : Proof.context -> JClause.T -> ((JLit.lpos * JClause.cpos) * (JLit.lpos * JClause.cpos)) -> JClause.T list
  val infer_arg_cong : Proof.context -> clause_lit -> JClause.T list
  val infer_bool_hoist : Proof.context -> clause_term -> JClause.T list
  val infer_false_elim : Proof.context -> clause_lit_side -> JClause.T list
  val simp_false_elim : Proof.context -> clause_lit_side -> JClause.T list
  val infer_bool_rw : Proof.context -> clause_term -> JClause.T list
  val infer_eq_hoist : Proof.context -> clause_term -> JClause.T list
  val infer_neq_hoist : Proof.context -> clause_term -> JClause.T list
  val infer_forall_hoist : Proof.context -> clause_term -> JClause.T list
  val infer_exists_hoist : Proof.context -> clause_term -> JClause.T list
  val infer_forall_rw : Proof.context -> clause_term -> JClause.T list
  val infer_exists_rw : Proof.context -> clause_term -> JClause.T list
  val infer_neg_ext : Proof.context -> clause_lit -> JClause.T list
  val forward_simplify :
    Proof.context
    -> { forward: bool, cheap: bool }
    -> Slam_Clause_Set.T
    -> (int * JLit.lpos) Term_Index.T
    -> (int * JClause.full_pos) Term_Index.T
    -> Subsumption_Index.index
    -> JClause.T
    -> { simplifications: JClause.T list, archive: JClause.T list }
  val backward_simplify :
    Proof.context
    -> Slam_Clause_Set.T
    -> (int * JLit.lpos) Term_Index.T
    -> (int * JClause.full_pos) Term_Index.T
    -> Subsumption_Index.index
    -> JClause.T
    -> JClause.T list * JClause.T list * Slam_Clause_Set.T
  val infer_clauses :
    Proof.context -> Slam_Clause_Set.T -> JClause.T -> (int * JClause.full_pos) Term_Index.T
    -> JClause.T list
  datatype step_result = Unsat | MaybeSat | Next
  type prover_state =
    { context: Proof.context
    , countdown: int
    , passive: Slam_Passive_Set.T
    , active: Slam_Clause_Set.T
    , green_index: (int * JClause.full_pos) Term_Index.T
    , unit_index: (int * JLit.lpos) Term_Index.T
    , subsumption_index: Subsumption_Index.index
    , archive: JClause.T list
    }
  (* original exception + prover state before the exception was raised *)
  exception SLAM_EXCEPTION of exn * prover_state
  val given_clause_loop : bool -> prover_state -> step_result * prover_state
  val given_clause_step : prover_state -> step_result * prover_state
  val try_saturate : Proof.context -> term option -> thm list -> step_result * prover_state
  val make_clause_db : prover_state -> int -> JClause.T
  (* DEBUG *)
  val ml_bool_of : term -> bool
  val contains_syntactic_complementaries : JLit.T list -> bool
end

structure Slam : SLAM =
struct

type clause_lit = JClause.T * JClause.cpos * JClause.eligibility
type clause_lit_side = JClause.T * (JLit.lpos * JClause.cpos) * JClause.eligibility
type clause_term = JClause.T * JClause.full_pos * JClause.eligibility
type unit_clause = JClause.T * JLit.lpos * JClause.eligibility

(* oc function from the PhD thesis
logically:
  outer_clausify maxidx b s c = clauses of (if b then s else \<not>s) \<or> c
Distribute the first logical symbol (\<and>, \<or>, \<longrightarrow>) over the clause (removing prefix
of negations above and below) *)
(* fun outer_clausify_non_quant changed ctxt maxidx b (Const (@{const_name HOL.Not}, _) $ s) c = *)
fun outer_clausify_non_quant _ ctxt maxidx b (@{term "HOL.Not"} $ s) c =
      outer_clausify_non_quant { changed = true } ctxt maxidx (not b) s c
  | outer_clausify_non_quant _ ctxt _ b (Const (@{const_name HOL.disj}, _) $ s $ t) c =
    if b
      then [fold (JClause.add_literal ctxt) [JLit.of_term_signed b s, JLit.of_term_signed b t] c]
      else
        [ JClause.add_literal ctxt (JLit.of_term_signed b s) c
        , JClause.add_literal ctxt (JLit.of_term_signed b t) c
        ]
  | outer_clausify_non_quant _ ctxt _ b (Const (@{const_name HOL.conj}, _) $ s $ t) c =
    if b
      then
        [ JClause.add_literal ctxt (JLit.of_term_signed b s) c
        , JClause.add_literal ctxt (JLit.of_term_signed b t) c
        ]
      else [fold (JClause.add_literal ctxt) [JLit.of_term_signed b s, JLit.of_term_signed b t] c]
  | outer_clausify_non_quant _ ctxt maxidx b (Const (@{const_name HOL.implies}, _) $ s $ t) c =
      (* rewrite as disjunction, additional not will be removed in JLit.mk_pred *)
      outer_clausify_non_quant { changed = true } ctxt maxidx b (HOLogic.mk_disj (HOLogic.mk_not s, t)) c
  (* FIXME: Making HO Sup work p.7 says: never simplify \<longleftrightarrow>. What does this mean
  concretely? (Isabelle represents \<longleftrightarrow> as HOL.eq) *)
  | outer_clausify_non_quant _ ctxt _ b (Const (@{const_name HOL.eq}, _) $ s $ t) c =
      (* FIXME: Is JLit.mk going to be deterministic enough? *)
      [JClause.add_literal ctxt (JLit.mk (s, t, b)) c]
  | outer_clausify_non_quant { changed = true } ctxt _ b t c =
      [JClause.add_literal ctxt (JLit.of_term_signed b t) c]
  | outer_clausify_non_quant { changed = false } _ _ _ _ _ =
      []


fun outer_clausify ctxt maxidx b (Const (@{const_name HOL.All}, T) $ P) c =
      if b then
        (* \<forall>x. P x = \<top> \<leadsto> P ?x_oc *)
        let
          val Abs (name, _, _) = P
          val fresh_var = Var ((name, maxidx + 1), Term.domain_type (fastype_of P))
          val new_lit =
            JLit.of_term_signed true (JTerm.norm_beta_eta_qeta (P $ fresh_var))
        in
          [ (JClause.add_literal ctxt new_lit c, SOME (P, Slam_Common.Left fresh_var)) ]
        end
      else
        (* (\<forall>x. P x) = \<bottom> is the same as (\<exists>x. \<not>P x) = \<top> *)
        outer_clausify
          ctxt
          maxidx
          true
          (* \<beta>\<eta>Q\<eta>-normal form guarantees that P is a \<lambda>-expression. *)
          (Const (@{const_name HOL.Ex}, T) $ JTerm.negate_in_lambda P)
          c
  | outer_clausify ctxt maxidx b (Const (@{const_name HOL.Ex}, T) $ P) c =
      if b then
        let
          val abstract_over = Free ("outerclausifyabsvar002460177", domain_type (fastype_of P))
          val () = if (not (exists_subterm (fn Free (name, _) =>
            name = #1 (dest_Free abstract_over) | _ => false) P)) then () else error "outer_clausify: assertion failed"
          val choice_witness =
            JTerm.make_choice_witness abstract_over (P $ abstract_over)
          val { skolem_constant, skolem_constant_with_args, skolem_constant_definition } =
            JTerm.make_skolem_constant choice_witness
          val skolem = (skolem_constant, skolem_constant_with_args, skolem_constant_definition)
          val lit =
            JLit.of_term_signed true (JTerm.norm_beta_eta_qeta (P $ skolem_constant_with_args))
        in
          [ (JClause.add_literal ctxt lit c, SOME (P, Slam_Common.Right skolem)) ]
        end
      else
        (* (\<exists>x. P x) = \<bottom> is the same as (\<forall>x. \<not>P x) = \<top> *)
        outer_clausify
          ctxt
          maxidx
          true
          (* \<beta>\<eta>Q\<eta>-normal form guarantees that P is a \<lambda>-expression. *)
          (Const (@{const_name HOL.All}, T) $ JTerm.negate_in_lambda P)
          c
  | outer_clausify ctxt maxidx b s c =
      outer_clausify_non_quant { changed = false } ctxt maxidx b s c
      |> map (fn c => (c, NONE))

(*** Rules ***)

(** Simplification **)

(* FIXME: Make this a richer object. Things that could be wrapped up in a "tracer":
  * trace premises
  * trace unifiers
  * trace_concl
  * fail <- how to make this polymorphic?
    Distinguish
    * calculus side condition related fail (ordering, ...)
    * lazy implementation related fail (prob. don't care about these)
    * no unifiers
  * Logic to collect messages and only decide whether to fire them at the end (e.g. produce no
    tracing output if there are no unifiers) or if there is an exception
*)
fun mk_tracer ctxt channel inference_name msg =
  channel ctxt (fn () => inference_name ^ ": " ^ msg ())

fun trace_concl ctxt (tracer: (unit -> string) -> unit) =
  tap (fn concl => (tracer (fn () => ("concl: " ^ JClause.pretty_clause ctxt concl))))

(* Syntactic tautology deletion 1 (TD1) (Schulz) *)
fun contains_syntactic_equation [] = false
  | contains_syntactic_equation c =
      exists (fn lit =>
        let val (s, t, is_positive) = JLit.dest lit in is_positive andalso s aconv t end) c

(* The condition `norm (negate l) = l'` is not equivalent to `l = norm (negate l')` so we need to
compare the negation of each literal to all other literals. *)
fun impl_contains_syntactic_complementaries _ [] = false
  | impl_contains_syntactic_complementaries previous_ls (l :: later_ls) =
      exists (curry JLit.aconv (JLit.norm_negative_pred (JLit.negate l))) previous_ls orelse
      exists (curry JLit.aconv (JLit.norm_negative_pred (JLit.negate l))) later_ls orelse
      impl_contains_syntactic_complementaries (l::previous_ls) later_ls

val contains_syntactic_complementaries = impl_contains_syntactic_complementaries []

(* FIXME: implement semantic tautology deletion? *)

(* Deletion of duplicated literals (DD) (Schulz) *)
fun simp_delete_duplicated_lits ctxt c =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_delete_duplicated_lits "(DD)"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)

    val literals = JClause.literals c
    (* positions of duplicates in the clause, critically in reverse order *)
    val cposs_of_dups =
      fold_index
        (fn (i, l) => fn dup_is =>
          (case get_index (curry JLit.aconv_as l) literals of
              NONE => error "simp_delete_duplicated_lits: didn't find literal itself"
            | SOME (index_of_existing, orientation) =>
                if i = index_of_existing
                  then dup_is (* found ourselves, not a duplicate *)
                  else {duplicate_of = index_of_existing, duplicate = i, orientation = orientation}::dup_is))
        literals
        []
    (* FIXME: use JClause.delete_lits_at *)
    val c' = fold (JClause.delete_lit_at ctxt) (map #duplicate cposs_of_dups) c
  in
    if JClause.length c' = JClause.length c
      then fail NONE (K "no duplicated lits")
      else
        (tracer (fn () => "deleted duplicated literals in " ^ JClause.pretty_clause ctxt c);
        SOME (
          c'
          |> JClause.recompute_selected ctxt
          |> JClause.refresh_id ctxt ()
          |> JClause.set_origin ctxt
            (Slam_Log.DeleteDuplicatedLits
              { premise = JClause.id c, duplicate_cposs = cposs_of_dups })
          |> trace_concl ctxt tracer
        ))
  end

(* Deletion of resolved literals (DR) (Schulz) *)
fun simp_delete_resolved_lits ctxt c =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_delete_resolved_lits "(DR)"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)

    (* literal of the from s \<noteq> s *)
    fun is_false_disequation l =
      let
        val (s, t, is_positive) = JLit.dest l
      in
        not is_positive andalso s aconv t
      end
    val cposs =
      c
      |> JClause.literals
      |> map_index (fn x => x)
      |> filter (is_false_disequation o snd)
      |> map fst
    val c' = JClause.delete_lits_at ctxt cposs c
  in
    if JClause.length c' = JClause.length c
      then fail NONE (K "no resolved lits")
      else
        (tracer (fn () => "deleted resolved literals in " ^ JClause.pretty_clause ctxt c);
        SOME (
          c'
          |> JClause.recompute_selected ctxt
          |> JClause.refresh_id ctxt ()
          |> JClause.set_origin ctxt
            (Slam_Log.DeleteResolvedLits { premise = JClause.id c, cposs = cposs })
          |> trace_concl ctxt tracer
        ))
  end

(* Rewriting of positive (RP) or negative literals (RN) simplification (Schulz) *)
(* FIXME: Implement side conditions following
  https://github.com/leanprover-community/duper/blob/aab52219c72cb52951832c8e985e1dc3e9497af9/Duper/Rules/Demodulation.lean#L51
*)
fun impl_simp_rewrite_lits ctxt (unit_clause, lp, JClause.Unknown) (target_clause, j as (_, _, target_cp), JClause.Unknown) =
  let
    val tracer =
      mk_tracer ctxt Slam_Common.trace_msg_rewrite_lits "(RP/RN)"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val () = tracer (fn () =>
      JClause.pretty_oriented ctxt unit_clause (lp, 0) ^ " into " ^ JClause.pretty_subterm ctxt target_clause j)
  in
  if not (JClause.is_positive_unit unit_clause) then fail NONE (K "not a positive unit") else
  let
  val positive = JLit.is_positive (JClause.lit_at target_cp target_clause)
  (* in particular: ensure the variables of `to` are distinct from those of target_clause *)
  val unit_shift = JClause.maxidx target_clause + 1
  val unit_clause = JClause.incr_indexes unit_shift unit_clause

  val from_eq_to = JLit.orient lp (JClause.the_unit_lit unit_clause)
  val (from, to, true) = JLit.dest from_eq_to (* Schulz: (s, t) *)

  val target_term = JClause.subterm_at_full_pos target_clause j (* Schulz: u *)
  val matchers =
    Slam_Unify.matchers
      (Context.Proof ctxt)
      (JClause.maxidx_of2 (unit_clause, target_clause))
      [(from, target_term)]

  fun build_conclusion matcher =
    let
      val () = tracer (K "build_conclusion")
      val msg = (fn () => "rewriting in " ^ JClause.pretty_subterm ctxt target_clause j
        ^ " with " ^ JClause.pretty_oriented ctxt unit_clause (lp, 0))
      val from_eq_to = JLit.norm_beta_eta_qeta_env matcher from_eq_to
      val from_cmp_to = JLit.kbo_compare_left_to_right from_eq_to
      val (from, to, true) = JLit.dest from_eq_to
    in
      (* NOTE: subst_term is only for Pattern.match, not Unify.matchers! *)
      if SOME GREATER <> from_cmp_to then
        fail NONE (fn () =>
          "s\<sigma> !\<succ> t\<sigma>: "
          ^ Slam_Common.pretty_term ctxt from
          ^ " !\<succ> "
          ^ Slam_Common.pretty_term ctxt to) else
      let
        val rewritten_clause =
          target_clause
          |> JClause.map_at_full_pos j (K to)
          |> JClause.norm_beta_eta_qeta ctxt
          (* FIXME: Envir.maxidx_of does not always return the correct maxidx of the instantiated
          terms. Why? Need a TVar maxidxforcer? *)
          |> JClause.set_maxidx (Envir.maxidx_of matcher)
          |> JClause.recalculate_maxidx
        val rewriting_clause = JClause.dummy [from_eq_to]
        val rewriting_smaller_than_rewritten = (fn () =>
          SOME LESS = JClause.kbo (rewriting_clause, rewritten_clause))
      in
        if positive andalso not (rewriting_smaller_than_rewritten ()) then
          fail NONE (K "rewriting not smaller than rewritten") else
        (tracer msg;
        (JClause.norm_beta_eta_qeta ctxt rewritten_clause)
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ctxt ()
        |> JClause.set_origin ctxt (
            (if positive then Slam_Log.RewritePositiveLits else Slam_Log.RewriteNegativeLits)
              { unit = JClause.id unit_clause
              , unit_shift = unit_shift
              , unit_orientation = lp
              , right_premise = JClause.id target_clause
              , subterm = j
              , substitution = matcher}
           )
        |> trace_concl ctxt tracer
        |> SOME)
      end
    end
    val report_no_matchers =
      Seq.pull
      #> tap (fn r => if is_none r then fail () (K "no matchers") else ())
      #> K
      #> Seq.make
  in
    matchers
    |> report_no_matchers
    |> Seq.take (Slam_Common.get_unifier_cutoff ctxt) 
    |> Seq.map_filter build_conclusion
    |> Seq.pull
    |> Slam_Common.map_some #1
  end end

(* Rewriting of positive literals (RP) simplification (Schulz) *)
(* Rewriting of positive literals (RN) simplification (Schulz) *)
val simp_rewrite_lits = impl_simp_rewrite_lits

(* active units rewrite given clause *)
fun forward_rewrite ctxt active unit_index given_clause =
  let
    val all_disabled = Config.get ctxt Slam_Common.disable_all
    fun cfg_rule rule = if not all_disabled orelse Config.get ctxt rule then true else false
    val cfg_rewrite_lits = cfg_rule Slam_Common.rule_rewrite_lits
    val green_subterms_in_given_clause =
      JClause.green_full_poss_of given_clause
      |> map (`(JClause.subterm_at_full_pos given_clause))
    fun candidate_units t : (JClause.T * JLit.lpos) list =
      Term_Index.get_generalizations t unit_index
      (* FIXME: replace this by `map`, once we delete from the index. *)
      |> map_filter (fn (id, lp) =>
        case Slam_Clause_Set.lookup active id of
          SOME active_clause => SOME (active_clause, lp)
        | NONE => NONE)
  in
    if not cfg_rewrite_lits then NONE else
    (* FIXME: do all possible rewrites, instead of only one and re-querying every time *)
    green_subterms_in_given_clause
    |> get_first (fn (t, fp) =>
    candidate_units t
    |> get_first (fn (c, lp) =>
      simp_rewrite_lits ctxt (c, lp, JClause.Unknown) (given_clause, fp, JClause.Unknown)
    ))
  end

fun forward_rewrite_bottom_up
  ctxt
  active
  unit_index
  given_clause
  : { clause : JClause.T, archive : JClause.T list }
=
  let
    fun forward_rewrite_subterm fp c : JClause.T option =
      (* invariant: fp is a valid green full pos for c *)
      let
        val subterm: term = JClause.subterm_at_full_pos c fp
      in
        Term_Index.get_first_of_generalizations
          subterm
          unit_index
          ( fn (active_unit_id, orientation) =>
              case Slam_Clause_Set.lookup active active_unit_id of
                NONE => NONE
              | SOME active_unit =>
                  impl_simp_rewrite_lits
                    ctxt
                    (active_unit, orientation, JClause.Unknown)
                    (c, fp, JClause.Unknown)
          )
      end
    fun repeat_forward_rewrite_subterm countdown fp (state as { clause, archive }) =
      if countdown < 0
        then
          ( warning "forward_rewrite_bottom_up: slam_forward_rewrite_countdown exhausted"
          ; state
          )
        else
          case forward_rewrite_subterm fp clause of
            NONE => state
          | SOME rewritten_clause =>
              repeat_forward_rewrite_subterm
                (countdown - 1)
                fp
                { clause = rewritten_clause, archive = clause :: archive }
    fun fold_postorder_over_green_full_pos (f : JClause.full_pos -> 'a -> 'a) : JClause.T -> 'a -> 'a =
      JClause.fold_postorder_with_green_full_pos (fn fp => fn _ => f fp)
  in
    fold_postorder_over_green_full_pos
      (repeat_forward_rewrite_subterm (Config.get ctxt Slam_Common.forward_rewrite_countdown))
      given_clause
      { clause = given_clause, archive = [] }
  end

(* given clause (a unit) rewrites active clauses *)
fun backward_rewrite ctxt active green_index given_clause
  : { simplifications : JClause.T list, archive : JClause.T list }
=
  if not (JClause.is_unit given_clause) then { simplifications = [], archive = [] } else
  let
    val all_disabled = Config.get ctxt Slam_Common.disable_all
    fun cfg_rule rule = if not all_disabled orelse Config.get ctxt rule then true else false
    val cfg_rewrite_lits = cfg_rule Slam_Common.rule_rewrite_lits
    fun backward_rewrite_oriented lp acc =
      let
        val candidate_subterms_in_active_clauses =
          Term_Index.get_instances
            (JClause.subterm_at_full_pos given_clause ([], lp, 0))
            green_index
        fun go (id, fp) (acc as { simplifications = simplifications, archive = archive }) =
          (* We don't update neither index nor active set, but instead check if the active clause is
            in the archive (indicating it is has already been simplified and is about to be
            deactivated after backward_rewrite returns).
            Conceptually: up-to-date active set = old active set - archive. *)
          (case find_first (curry op= id o JClause.id) archive of
            SOME _ => acc (* skip *)
          | NONE => (case Slam_Clause_Set.lookup active id of
              SOME active_clause =>
                ( case if cfg_rewrite_lits then (simp_rewrite_lits ctxt (given_clause, lp, JClause.Unknown) (active_clause, fp, JClause.Unknown)) else NONE of
                    SOME result => { simplifications = result::simplifications, archive = active_clause::archive }
                  | NONE => acc
                )
            | NONE =>
              (* FIXME: error here, once we delete from the index. *)
              (* error "clause was not deleted from index" *)
              acc))
      in
        fold go candidate_subterms_in_active_clauses acc
      end
  in
    { simplifications = [], archive = [] }
    |> backward_rewrite_oriented JLit.Left
    |> backward_rewrite_oriented JLit.Right
  end

(* Negative simplify-reflect (NS) simplification (Schulz) *)
fun simp_negative_simplify_reflect ctxt (unit_clause, unit_lp) (target_clause, target_cp) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_negative_simplify_reflect "(NS)"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
  in
  if not (JClause.is_negative_unit unit_clause) then fail NONE (K "not a negative uniti") else
  if not (JLit.is_positive (JClause.lit_at target_cp target_clause))
    then fail NONE (K "literal to be deleted is not positive") else
  let
    val unit_shift = (JClause.maxidx target_clause + 1)
    val unit_clause = JClause.incr_indexes unit_shift unit_clause
    val maxidx = JClause.maxidx_of2 (unit_clause, target_clause)
    val (s, t, false) =
      JLit.dest (JLit.orient unit_lp (JClause.the_unit_lit unit_clause)) (* Schulz: s, t *)
    val (u, v, true) = JLit.dest (JClause.lit_at target_cp target_clause) (* Schulz: \<sigma>(s), \<sigma>(t) *)
    val matcher =
      [(s, u), (t, v)]
      |> Slam_Unify.matchers (Context.Proof ctxt) maxidx
      |> Seq.pull
    (* tracing *)
    val msg = (fn () => "   " ^ "(NS)"
      ^ " deleting highlighted literal of " ^ JClause.pretty_lit ctxt target_clause target_cp
      ^ " with " ^ JClause.pretty_clause ctxt unit_clause)
  in
    if is_some matcher
      then let val () = tracer msg in
        target_clause
        |> JClause.delete_lit_at ctxt target_cp
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ctxt ()
        |> JClause.set_origin ctxt (Slam_Log.NegativeSimplifyReflect
            { literal = target_cp
            , right_premise = JClause.id target_clause
            , unit = JClause.id unit_clause
            , matcher = #1 (the matcher)
            , unit_shift = unit_shift
            , unit_orientation = unit_lp }
           )
        |> trace_concl ctxt tracer
        |> SOME
      end
      else fail NONE (K "no match")
  end
  end

(* given terms s, t, the longest common position p such that s, t are equal except
for their subtrees at p *)
(* FIXME: rename to find_single_blue_disagreement and change appropriately *)
(* FIXME: how to deal with types???
    Just take types into consideration when comparing constant symbols and vars?
    Is there any other meaningful way of treating types (contrived: extend the
    notion of subterm to types, extend the notion of path to index into types as
    well, etc.) ?
    How much follows from well-typedness of the equality literal? -> at least
    that [] is a disagreement position
*)
fun find_single_green_disagreement ctxt term_pair =
  let
    val disagreement_pos = JTerm.disagreement_tpos_of2 term_pair
    fun chop_end_until_green term tpos =
      if JTerm.is_green_tpos tpos term
        then tpos
        else chop_end_until_green term (fst (split_last tpos))
    val green_disagreement_pos =
      Slam_Common.map_some (chop_end_until_green (fst term_pair)) disagreement_pos
  in
    green_disagreement_pos
  end

(* implementation of positive simplify-reflect and equality subsumption *)
fun literal_can_match_single_disagreement
      ctxt (unit_maxidx, unit_lit) (target_maxidx, target_lit) =
  let
    val unit_shift = target_maxidx + 1
    val unit_lit =
      unit_lit |> JLit.map (Logic.incr_indexes ([], unit_shift))
    val maxidx = unit_maxidx + target_maxidx + 1
    val (lhs, rhs, true) = JLit.dest unit_lit (* Schulz: s, t *)
    val (target_lhs, target_rhs, _) = JLit.dest target_lit (* Schulz: u[], u[]*)
    (* Schulz: longest possbile p *)
    val longest_prefix_of_disagreements =
      find_single_green_disagreement ctxt (target_lhs, target_rhs)
    fun match_disagreement_position prefix_of_disagreements =
      let
        val (target_term_lhs, target_term_rhs) = (* u|\<^sub>p *)
          (JTerm.subterm_at target_lhs prefix_of_disagreements,
          JTerm.subterm_at target_rhs prefix_of_disagreements)
        val matcher =
          ( [(lhs, target_term_lhs), (rhs, target_term_rhs)]
          , [(lhs, target_term_rhs), (rhs, target_term_lhs)] )
          |> apply2 (Slam_Unify.matchers (Context.Proof ctxt) maxidx)
          |> (fn (left_matchers, right_matchers) =>
            (Seq.map (pair JLit.Left) left_matchers, Seq.map (pair JLit.Right) right_matchers))
          |> Seq.interleave
          |> Seq.pull
          |> Slam_Common.map_some fst
      in
        Slam_Common.map_some (pair prefix_of_disagreements) matcher
      end
  in
      case longest_prefix_of_disagreements of
        NONE => NONE (* terms are equal, (TD1) or (DR) will take care of it *)
      | SOME longest_prefix_of_disagreements =>
          (* Schulz' p is any of the prefixes of the longest possible p *)
          fold (fn position => fn matcher =>
            case matcher of SOME m => SOME m | NONE => match_disagreement_position position)
          (prefixes longest_prefix_of_disagreements)
          NONE
          |> Slam_Common.map_some (pair unit_shift)
  end

(* Positive simplify-reflect (PS) simplification (Schulz)
      s = t    u\<langle>\<sigma>(s)\<rangle>\<^sub>p \<noteq> u\<langle>\<sigma>(t)\<rangle>\<^sub>p \<or> R
      --------------------------------
      s = t              R
*)
fun simp_positive_simplify_reflect ctxt unit_clause (target_clause, target_cp) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_positive_simplify_reflect "(PS)"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
  in
  if not (JClause.is_positive_unit unit_clause) then fail NONE (K "not a positive unit") else
  if not (JLit.is_negative (JClause.lit_at target_cp target_clause)) then
    fail NONE (K "literal to be deleted is not negative") else
  let
    val lit = JClause.the_unit_lit unit_clause (* Schulz: s, t *)
    val target_lit = JClause.lit_at target_cp target_clause (* Schulz: u[], u[]*)
    val matcher =
      literal_can_match_single_disagreement
        ctxt
        (JClause.maxidx unit_clause, lit)
        (JClause.maxidx target_clause, target_lit)
    (* tracing *)
    val msg = (fn () =>
      (* FIXME: implement pretty_subterms to highlight both subterms *)
      " deleting highlighted lit in " ^ JClause.pretty_lit ctxt target_clause target_cp
      ^ " with " ^ JClause.pretty_clause ctxt unit_clause)
  in
    case matcher of
      SOME (unit_shift, (disagreement, (unit_orientation, matcher))) =>
        let val () = tracer msg in
        target_clause
        |> JClause.delete_lit_at ctxt target_cp
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ctxt ()
        |> JClause.set_origin ctxt (
            Slam_Log.PositiveSimplifyReflect
            { unit = JClause.id unit_clause
            , unit_shift = unit_shift
            , matcher = matcher
            , unit_orientation = unit_orientation
            , right_premise = JClause.id target_clause
            (* This fixed to be JLit.Left because there is symmetry in the orientation of the unit
            and which side of the target literal we apply the rewrite to. *)
            , disagreement = (disagreement, JLit.Left, target_cp) }
          )
        |> trace_concl ctxt tracer
        |> SOME
        end
      | NONE => fail NONE (K "no match")
  end
  end

(* Equality subsumption (ES) redundancy check (Schulz) *)
fun equality_subsumes ctxt (unit_clause, target_clause) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_equality_subsumption "(ES)"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
  in
  if not (JClause.is_positive_unit unit_clause) then fail false (K "not a positive unit") else
  let
    (* Schulz: s, t *)
    val unit_lit = (JClause.maxidx unit_clause, JClause.the_unit_lit unit_clause)
    val positive_lits =
      JClause.literals target_clause
      |> filter JLit.is_positive
      |> map (pair (JClause.maxidx target_clause))
    val exists_matcher =
      exists (is_some o literal_can_match_single_disagreement ctxt unit_lit) positive_lits
    (* FIXME: better tracing, pretty_subterms *)
    val _ =
      if exists_matcher
        then
          tracer (fn () => "equality subsumed by " ^ JClause.pretty_clause ctxt unit_clause)
        else fail () (K "no match")
  in
    exists_matcher
  end
  end

fun is_trivial c =
  contains_syntactic_equation (JClause.literals c) orelse
  contains_syntactic_complementaries (JClause.literals c)

(* FIXME: given_clause is a misnomer, as it could also (potentially) be a simplification result. But
maybe we shouldn't check simplification results that we add to the passive set for subsumption.
Pros: We don't re-do all the subsumption checks against unchanged actives, by the time the
  simplified clause comes around again.
Cons: We miss out on the subsumption check by the given_clause (which is a sister clause of the
  simplified clause)
There is a middle ground, where we put the clause back into the passive set, but also remember,
against which clauses we checked for subsumption, and w.r.t. which clauses we already performed
simplifications.
*)
fun is_forward_subsumed ctxt clause active subsumption_index : bool =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_clause_subsumption "(CS)"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)

    val () = tracer (fn () => "forward subsumption of " ^ JClause.pretty_clause ctxt clause)

    fun trace_subsumer subsuming_clause subsumed =
      (if subsumed
          then tracer (fn () => "subsumed by " ^ JClause.pretty_clause ctxt subsuming_clause)
          else fail () (fn () => "not subsumed by " ^ JClause.pretty_clause ctxt subsuming_clause);
      subsumed)
    val all_disabled = Config.get ctxt Slam_Common.disable_all
    fun if_cfg rule f = if not all_disabled orelse Config.get ctxt rule then f () else false

    fun clause_subsumed_by active_clause_id =
      (case Slam_Clause_Set.lookup active active_clause_id of
        SOME active_clause =>
          if_cfg
            Slam_Common.rule_clause_subsumption
            (fn _ => Slam_Subsumption.subsumes (Context.Proof ctxt) (active_clause, clause)
              |> trace_subsumer active_clause)
      | NONE => false)

    fun is_subsumed_folder active_id already_subsumed =
      already_subsumed orelse clause_subsumed_by active_id

    val subsumed =
      Subsumption_Index.fold_subsuming clause is_subsumed_folder subsumption_index false
  in
    subsumed
  end

fun get_backward_subsumed ctxt given_clause active subsumption_index =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_clause_subsumption "(CS)"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)

    val () = tracer (fn () => "backward subsumption by " ^ JClause.pretty_clause ctxt given_clause)

    fun trace_subsumer subsuming_clause subsumed =
      (if subsumed
          then tracer (fn () => "subsumed by " ^ JClause.pretty_clause ctxt subsuming_clause)
          else fail () (fn () => "not subsumed by " ^ JClause.pretty_clause ctxt subsuming_clause);
      subsumed)

    val all_disabled = Config.get ctxt Slam_Common.disable_all
    fun if_cfg rule f = if not all_disabled orelse Config.get ctxt rule then f () else false

    fun fetch_if_subsumed_by_given_clause active_clause_id =
      (case Slam_Clause_Set.lookup active active_clause_id of
        SOME active_clause =>
          if (
            if_cfg
              Slam_Common.rule_clause_subsumption
              (fn _ => Slam_Subsumption.subsumes (Context.Proof ctxt) (given_clause, active_clause)
                |> trace_subsumer given_clause)
          ) then SOME active_clause else NONE
      | NONE => NONE)

    val subsumed_candidates =
      Subsumption_Index.fold_subsumed given_clause (curry op::) subsumption_index []

    val subsumed_actives = map_filter fetch_if_subsumed_by_given_clause subsumed_candidates
  in
    subsumed_actives
  end

(* FIXME: implement forwards and backwards variants using indexing *)
fun is_equality_subsumed ctxt active c =
  let
    val all_disabled = Config.get ctxt Slam_Common.disable_all
    (* val _ = if all_disabled then writeln "REDUNDANCY CHECKS DISABLED" else () *)
    fun if_cfg rule f = if not all_disabled orelse Config.get ctxt rule then f () else false
    fun equality_subsumed_by active_clause =
      if_cfg
        Slam_Common.rule_equality_subsumption
        (fn _ => equality_subsumes ctxt (active_clause, c))
  in
    Slam_Clause_Set.exists equality_subsumed_by active
  end

(** Clausification **)

(* FIXME: duplicate *)
fun ml_bool_of @{term True} = true
  | ml_bool_of @{term False} = false
  | ml_bool_of _ = error "term is not HOL.True or HOL.False"

fun hol_bool_of true = @{term "True"}
  | hol_bool_of false = @{term "False"}
  | hol_bool_of _ = error "term is not true of false"

(* PosOuterClaus and NegOuterClaus simplficiations *)
fun simp_bool_outer_claus ctxt (c, i, JClause.Unknown) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_simp_outer_claus "OuterClaus"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val () = tracer (fn () => "start: " ^ JClause.pretty_clause ctxt c)

    val lit = JClause.lit_at i c
  in
  if not (JLit.is_pred lit) then
    fail [] (fn () => "not a predicate literal: " ^ JLit.pretty_lit ctxt lit) else
  let
    val maxidx = JClause.maxidx c
    val (s, b) = lit |> JLit.dest_pred ||> ml_bool_of
    val c' = JClause.delete_lit_at ctxt i c
    (* Meaning: "if b then PosOuterClaus else NegOuterClaus" *)
    val clausified = outer_clausify ctxt maxidx b s c'
  in
    if null clausified then
      (* in particular if head of s is not a logical symbol *)
      fail [] (fn () => "no clausification results for " ^ JLit.pretty_lit ctxt lit) else
    clausified
    |> map_index
      (fn (index, (clause, quant_info)) =>
        clause
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.set_origin ctxt (
          Slam_Log.SimpPosNegOuterClaus
            { premise = JClause.id c
            , literal = i
            , conclusion_index = index
            , quant_info = quant_info
            }
        )
        |> trace_concl ctxt tracer
      )
    (* FIXME: map might be sufficient, i.e. no need for a fold *)
    |> (fn clauses =>
        fold
          (fn clause => fn (unit_value, acc) =>
            (unit_value, JClause.refresh_id ctxt unit_value clause :: acc))
          clauses
          ((), [])
       )
    |> #2
  end
  end

(* EqOuterClaus and NeqOuterClaus inferences *)
fun infer_eq_neq_outer_claus ctxt (c, i, eligibility) =
  let
    val (s, t, b) = JLit.dest (JClause.lit_at i c)
  in
    if (Runtime.exn_trace (fn () =>
          not (fastype_of s = @{typ bool} andalso fastype_of t = @{typ bool})
    ))
      then error "not boolean equation"
    (* FIXME: set origin *)
    else if b
      then (* EqOuterClaus *)
        [ fold (JClause.add_literal ctxt) [JLit.mk_pred s false, JLit.mk_pred t true] c
        , fold (JClause.add_literal ctxt) [JLit.mk_pred s true, JLit.mk_pred t false] c
        ]
      else (* NeqOuterClaus *)
        [ fold (JClause.add_literal ctxt) [JLit.mk_pred s false, JLit.mk_pred t false] c
        , fold (JClause.add_literal ctxt) [JLit.mk_pred s true, JLit.mk_pred t true] c
        ]
  end

(*
fun impl_infer_sup precheck ctxt (d, (lp, cp), (c, u_pos)) =
  let
    (* rename, FIXME: let caller decide this *)
    val d = JClause.incr_indexes (JClause.maxidx c + 1) d
    val env = Envir.empty (JClause.maxidx_of2 (c, d))
    (* unpack *)
    val rewriting_literal = JClause.lit_at cp d (* t \<approx> t' *)
    val (t, t', is_pos_eq) = JLit.orient lp rewriting_literal
    val u = JClause.subterm_at_full_pos c u_pos
  in
    (* first round of checks *)
    if not (precheck is_pos_eq u c) then [] else
    let
      val unifiers = Slam_Unify.smash_unifiers (Context.Proof ctxt) [(t, u)] env
    in
      error "impl_infer_sup unimplemented"
    end
  end
*)

fun variable_condition ctxt u =
  case Slam_Common.get_sup_variable_condition ctxt of
    Slam_Common.None => NONE
  | Slam_Common.FirstOrder =>
      if JTerm.is_variable_headed u
        then SOME "u is variable headed"
        else NONE
  | Slam_Common.Approximate =>
      error "approximate sup variable condition unimplemented"

(* Sup inference *)
fun infer_sup ctxt (d, (lp, cp), tt'_eligibility) (c, u_pos, u_eligibility) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_sup "Sup"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val () = tracer (fn () =>
      JClause.pretty_oriented ctxt d (lp, cp) ^ " into " ^ JClause.pretty_subterm ctxt c u_pos)
    val left_premise_shift = JClause.maxidx c + 1
    val d = JClause.incr_indexes left_premise_shift d
    val env = Envir.empty (JClause.maxidx_of2 (c, d))
    val rewriting_literal = JClause.lit_at cp d (* t \<approx> t' *)
    val (t, t', is_pos_eq) = JLit.dest (JLit.orient lp rewriting_literal)
    val u = JClause.subterm_at_full_pos c u_pos
  in
    if not is_pos_eq then fail [] (K "not positive") else
    if (not (Config.get ctxt Slam_Common.sup_into_fluid) andalso JTerm.might_be_fluid u)
      then fail [] (K "might be fluid") else (* 1 *)
    if (not (Config.get ctxt Slam_Common.sup_into_deeply_occuring)
        andalso (is_Var u andalso JClause.occurs_deeply u c))
      then fail [] (K "deeply occuring var") else (* 2 *)
    case variable_condition ctxt u of SOME msg => fail [] (K msg) | NONE =>
    let
      val () = tracer (fn () =>
        Slam_Common.pretty_term ctxt t ^ " ?= " ^ Slam_Common.pretty_term ctxt u)
      val unifiers = Slam_Unify.smash_unifiers (Context.Proof ctxt) [(t, u)] env
      val (unifiers, _) = Seq.chop (Slam_Common.get_unifier_cutoff ctxt) unifiers
      val () = if 0 = length unifiers then fail () (K "no unifiers") else ()
      fun build_conclusion unifier =
        let
          val (c, d) =
            (c, d)
            |> apply2 (JClause.norm_beta_eta_qeta_env ctxt unifier)
            |> apply2 (JClause.recompute_selected ctxt)
          fun u_eligible () = JClause.is_eligible_full_pos c (u_pos, u_eligibility)
          (* This checks for strict eligibility of cp because the literal at cp is positive. *)
          fun tt'_eligible () = JClause.is_eligible_cpos d (cp, tt'_eligibility)
          (* val _ = writeln ("c_comp_d " ^ @{make_string} c_comp_d) *)
          fun d' () = JClause.delete_lit_at ctxt cp d
          (* this relies on normalization not destroying green / top level positions, i.e.
          (t = t')\<sigma> = (t\<sigma> = t'\<sigma>) and C<u>\<sigma> = C\<sigma><u\<sigma>> *)
          val t_eq_t' = JLit.orient lp (JClause.lit_at cp d)
          val (t, t', _) = JLit.dest t_eq_t'
          fun ct' () = JClause.map_at_full_pos u_pos (K t') c
          fun t_cmp_t' () = JLit.kbo_compare_left_to_right t_eq_t'
        in
          (* order restrictions *)
          if Partial_Ord.is_less_equal (t_cmp_t' ()) then
            fail NONE (fn () => "t\<sigma> \<preceq> t'\<sigma>: " ^
              Slam_Common.pretty_term ctxt t ^ " \<preceq> " ^ Slam_Common.pretty_term ctxt t') else (* 5 *)
          if not (Config.get ctxt Slam_Common.sup_into_non_eligible) andalso not (u_eligible ()) then fail NONE (fn () => ("u not eligible in " ^ JClause.pretty_subterm ctxt c u_pos)) else (* 6 *)
          (* according to the thesis, side condition 7 is skipped for performance reasons *)
          if not (Config.get ctxt Slam_Common.sup_from_non_eligible) andalso not (tt'_eligible ()) then fail NONE (fn () => ("t \<approx> t' not eligible in" ^ JClause.pretty_clause ctxt d)) else (* 8 *)
          (* FXIME 9. 10. *)
          JClause.combine ctxt (d' ()) (ct' ())
          |> JClause.norm_negative_predicate_literals ctxt
          |> JClause.recompute_selected ctxt
          |> JClause.refresh_id ctxt ()
          |> JClause.set_origin ctxt
              (Slam_Log.Sup
                { left_premise = JClause.id d
                , left_premise_shift = left_premise_shift
                , right_premise = JClause.id c
                , literal = (lp, cp)
                , subterm = u_pos
                , substitution = unifier })
          |> trace_concl ctxt tracer
          |> SOME
        end
    in
      map_filter build_conclusion unifiers
    end
  end

(* given clause as the left premise of superposition *)
fun sup_given_into_active
  (ctxt : Proof.context)
  (given_clause : JClause.T)
  (active : Slam_Clause_Set.T)
  (green_index: (int * JClause.full_pos) Term_Index.T)
  : JClause.T list
=
  let
    (* the equality literals that are being eliminated *)
    val ts_in_given_clause : (term * ((JLit.lpos * JClause.cpos) * JClause.eligibility)) list =
      if Config.get ctxt Slam_Common.sup_from_non_eligible
        then
          (Slam_Common.cartesian_product
            [JLit.Left, JLit.Right]
            (JClause.positive_cposs_of given_clause)
          )
          |> map (fn (lp, cp) =>
              (JClause.subterm_at_full_pos given_clause ([], lp, cp), ((lp, cp), JClause.Unknown))
          )
        else
          (Slam_Common.cartesian_product
            [JLit.Left, JLit.Right]
            (JClause.potentially_eligible_positive_cposs_of given_clause)
          )
          |> map (fn (lp, (cp, eligibility)) =>
              (JClause.subterm_at_full_pos given_clause ([], lp, cp), ((lp, cp), eligibility))
          )
    fun candidate_green_subterms t : (JClause.T * JClause.full_pos * JClause.eligibility) list =
      Term_Index.get_unifiables t green_index
      (* FIXME: replace this by `map`, once we delete from the index. *)
      |> map_filter (fn (id, fp) =>
        case Slam_Clause_Set.lookup active id of
          SOME active_clause =>
            if Config.get ctxt Slam_Common.sup_into_non_eligible
              then
                SOME (active_clause, fp, JClause.Unknown)
              else
                (case JClause.is_potentially_eligible_full_pos active_clause fp of
                  SOME eligibility => SOME (active_clause, fp, eligibility)
                | NONE => NONE)
          | NONE => NONE)
  in
    ts_in_given_clause
    |> maps (fn (t, ((lp, cp), eligibility)) =>
        candidate_green_subterms t
        |> maps (fn clause_term =>
            infer_sup ctxt (given_clause, (lp, cp), eligibility) clause_term))
  end

(* given clause as the right premise of superposition *)
fun sup_active_into_given
  (ctxt : Proof.context)
  (given_clause : JClause.T)
  (active : Slam_Clause_Set.T)
  (green_index: (int * JClause.full_pos) Term_Index.T)
  : JClause.T list
=
  let
    val green_subterms_given : (term * JClause.full_pos * JClause.eligibility) list =
      if Config.get ctxt Slam_Common.sup_into_non_eligible
        then
          JClause.green_full_poss_of given_clause
          |> map (fn fp => (JClause.subterm_at_full_pos given_clause fp, fp, JClause.Unknown))
        else
          JClause.potentially_eligible_green_full_poss_of given_clause
          |> map (fn (fp, eligibility) => (JClause.subterm_at_full_pos given_clause fp, fp, eligibility))
    fun candidate_active_lits t : (JClause.T * (JLit.lpos * JClause.cpos) * JClause.eligibility) list =
      Term_Index.get_unifiables t green_index
      |> map_filter (fn (id, fp) =>
           case fp of
             ([], lp, cp) =>
               (case Slam_Clause_Set.lookup active id of
                 SOME active_clause =>
                    if Config.get ctxt Slam_Common.sup_from_non_eligible
                      then
                        SOME (active_clause, (lp, cp), JClause.Unknown)
                      else
                        (case JClause.is_potentially_eligible_positive_cpos active_clause cp of
                          SOME eligibility => SOME (active_clause, (lp, cp), eligibility)
                        | NONE => NONE)
                 | NONE => NONE)
           | _ => NONE (* only want top-level terms *)
         )
  in
    green_subterms_given
    |> maps (fn (t, fp, eligibility) =>
        candidate_active_lits t
        |> maps (fn active_lit =>
            infer_sup ctxt active_lit (given_clause, fp, eligibility)))
  end

(* ERes inference *)
fun infer_eres (ctxt : Proof.context) (c, cp, eligibility) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_e_res "ERes"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val () = tracer (fn () =>
      "start: " ^ JClause.pretty_clause ctxt c ^ ", literal: " ^ @{make_string} cp)
    val (u, u', is_pos_eq) = JLit.dest (JClause.lit_at cp c)
    val unifiers =
      Slam_Unify.smash_unifiers (Context.Proof ctxt) [(u, u')] (Envir.empty (JClause.maxidx c))
    val (unifiers, _) = Seq.chop (Slam_Common.get_unifier_cutoff ctxt) unifiers
    fun build_conclusion unifier =
      let
        val () = tracer (K "build_conclusion")
        val c = c |> JClause.norm_beta_eta_qeta_env ctxt unifier |> JClause.recompute_selected ctxt
      in
        if not (JClause.is_eligible_cpos c (cp, eligibility)) then fail NONE (K "literal not eligible") else
        c
        |> JClause.delete_lit_at ctxt cp
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ctxt ()
        |> JClause.set_origin ctxt
          (Slam_Log.ERes { premise = JClause.id c, literal = cp, substitution = unifier })
        |> trace_concl ctxt tracer
        |> SOME
      end
  in
    if is_pos_eq
      then fail [] (K "not a negative literal")
      else map_filter build_conclusion unifiers
  end

(* EFact inference *)
fun infer_efact ctxt c ((lp', cp'), (lp, cp)) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_e_fact "EFact"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val () = tracer (fn () => "start: " ^ JClause.pretty_clause ctxt c)
    val (u', v', is_pos') = JLit.dest (JLit.orient lp' (JClause.lit_at cp' c))
    val (u, v, is_pos) = JLit.dest (JLit.orient lp (JClause.lit_at cp c))
    val () = tracer (fn () =>
      Slam_Common.pretty_term ctxt u ^ " ?= " ^ Slam_Common.pretty_term ctxt u')
    val unifiers =
      Slam_Unify.smash_unifiers (Context.Proof ctxt) [(u, u')] (Envir.empty (JClause.maxidx c))
    val (unifiers, _) = Seq.chop (Slam_Common.get_unifier_cutoff ctxt) unifiers
    val nothing_selected_in_c = JClause.selected c = []
    fun build_conclusion unifier =
      let
        val () = tracer (fn () => "build_conclusion")
        val c = c |> JClause.norm_beta_eta_qeta_env ctxt unifier
        val (u', v', _) = JLit.dest (JLit.orient lp' (JClause.lit_at cp' c))
        val uv_literal = JClause.lit_at cp c
        val (u, v, _) = JLit.dest (JLit.orient lp uv_literal)
        val u_v_comp = JLit.kbo_compare_left_to_right uv_literal
        val uv_maximal = Slam_Order.is_maximal JLit.kbo false uv_literal (JClause.literals c)
      in
        if Partial_Ord.is_less_equal u_v_comp then fail NONE (K "u\<sigma> \<preceq> v\<sigma>") else
        if not uv_maximal then fail NONE (K "u\<approx>v not maximal") else
        if not nothing_selected_in_c then fail NONE (K "something selected") else
        c
        |> JClause.delete_lit_at ctxt (Int.max (cp, cp'))
        |> JClause.delete_lit_at ctxt (Int.min (cp, cp'))
        |> JClause.add_literal ctxt (JLit.mk (v, v', false))
        |> JClause.add_literal ctxt (JLit.mk (u, v', true))
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ctxt ()
        |> JClause.set_origin ctxt
            (Slam_Log.EFact
              { premise = JClause.id c
              , left_literal = (lp', cp')
              , right_literal = (lp, cp)
              , substitution = unifier })
        |> trace_concl ctxt tracer
        |> SOME
      end
    in
      if not (is_pos andalso is_pos') then fail [] (K "negative literal") else
      if cp' = cp then fail [] (K "equal positions") else
      map_filter build_conclusion unifiers
    end

(* ArgCong inference

        C' \<or> s = s'
------------------------------- ArgCong
C'\<sigma> \<or> s\<sigma> x\<^sub>1 \<dots> x\<^sub>n = s'\<sigma> x\<^sub>1 \<dots> x\<^sub>n

* n > 0
* x\<^sub>i :: \<alpha>\<^sub>i fresh
* \<sigma> is the most general unifier that guarantees well typedness of the
  conclusion, so \<sigma> = mgu(type(s), \<alpha>\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> \<alpha>\<^sub>n \<Rightarrow> \<tau>) (Note: type(s) = type(s'))
* s = s' strictly >-eligible in C w.r.t \<sigma>

*)

fun infer_arg_cong ctxt (c, cpos, eligibility) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_arg_cong "ArgCong"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val () = tracer (fn () =>
      "start: " ^ JClause.pretty_clause ctxt c ^ ", literal: " ^ @{make_string} cpos)
    val (s, s', b) = JLit.dest (JClause.lit_at cpos c)
  in
  if not b then fail [] (K "negative literal") else
  let
    val s_num_of_args = length (Term.binder_types (fastype_of s))

    fun mk_fresh_typ idx = TVar (("'a", idx), Sign.defaultS (Proof_Context.theory_of ctxt))
    fun mk_fresh_var idx = Var (("x_ac", idx), mk_fresh_typ idx)

    val maxidx = JClause.maxidx c

    val new_maxidx = maxidx + s_num_of_args + (Slam_Common.get_arg_cong_extra_conclusions ctxt) + 1

    val fresh_result_type = mk_fresh_typ new_maxidx
    val xs_idxs = (maxidx + 1) upto (new_maxidx - 1)
    val fresh_variables = map mk_fresh_var xs_idxs

    fun build_conclusion fresh_variables =
      let
        val () = tracer (fn () => "build_conclusion")

        val function_type = (map fastype_of fresh_variables) ---> fresh_result_type

        val unifier =
          Pattern.unify_types
            (Context.Proof ctxt)
            (fastype_of s, function_type)
            (Envir.empty new_maxidx)

        val new_literal =
          (s, s')
          |> apply2 (fn t => list_comb (t, fresh_variables))
          |> (fn (x, y) => (x, y, true))
          |> JLit.mk

        val new_clause =
          c
          |> JClause.map_at_cpos cpos (K new_literal)
          |> JClause.norm_beta_eta_qeta_env ctxt unifier (* sets maxidx *)
          |> JClause.norm_negative_predicate_literals ctxt
          |> JClause.recompute_selected ctxt
          |> JClause.refresh_id ctxt ()
          |> JClause.set_origin ctxt
              (Slam_Log.ArgCong
                { premise = JClause.id c
                , substitution = unifier
                , literal = cpos
                , vars = map (JTerm.norm_beta_eta_qeta_env unifier) fresh_variables })
      in
        if not (JClause.is_eligible_cpos new_clause (cpos, eligibility)) then
          fail NONE (K "s\<sigma>\<approx>s'\<sigma> not strictly eligible in C\<sigma>") else
        new_clause
        |> trace_concl ctxt tracer
        |> SOME
      end
  in
    prefixes1 fresh_variables
    |> map_filter
        (fn vars =>
            build_conclusion vars handle Pattern.Unif => fail NONE (K "Pattern.Unif"))
  end
  end

fun infer_bool_hoist ctxt (c, (u_pos as (_, _, cpos)), eligibility) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_bool_hoist "BoolHoist"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val () = tracer (fn () => "start: " ^ JClause.pretty_clause ctxt c)
    val u = JClause.subterm_at_full_pos c u_pos
    val () = tracer (fn () => "u = " ^ Slam_Common.pretty_term ctxt u)
    val u_in_positive_lit = JLit.is_positive (JClause.lit_at cpos c)
    val u_eligible = JClause.is_eligible_full_pos c (u_pos, eligibility)
    val u_typ = fastype_of u
    (* raises TUNIFY (from Sign.typ_unify) *)
    fun build_conclusion _ =
      let
        val () = tracer (fn () => "build_conclusion")
        val (unifier, maxidx) =
          Sign.typ_unify
            (Proof_Context.theory_of ctxt)
            (u_typ, @{typ "HOL.bool"})
            (Vartab.empty, JClause.maxidx c)
        val u_eq_true = JLit.mk_eq u (@{term "HOL.True"})
        val unifier = Envir.Envir { maxidx = maxidx, tenv = Vartab.empty, tyenv = unifier }
      in
        if JTerm.is_variable_headed u (* 2. *) then fail [] (K "u variable headed") else
        if JClause.is_position_of_fully_applied_logical_symbol u_pos c (* 2. *) then
          fail [] (K "u is a fully applied logical symbol") else
        if not u_eligible (* 3. *) then fail [] (K "u not eligible") else
        if (u_in_positive_lit andalso [] = #1 u_pos) (* 4. *) then
          fail [] (K "u is at the top level of a positive literal") else
        c
        |> JClause.map_at_full_pos u_pos (K @{term "HOL.False"})
        |> JClause.add_literal ctxt u_eq_true
        |> JClause.norm_beta_eta_qeta_env ctxt unifier
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ctxt ()
        |> JClause.set_origin ctxt
          (Slam_Log.BoolHoist { premise = JClause.id c, subterm = u_pos, substitution = unifier })
        |> trace_concl ctxt tracer
        |> single
        end
  in
    (build_conclusion () handle Type.TUNIFY => fail [] (K "Type.TUNIFY"))
  end

fun impl_simp_infer_false_elim as_simplification ctxt (c, (lp, cp), eligibility) =
  let
    val tracer =
      if as_simplification then
        mk_tracer ctxt Slam_Common.trace_msg_simp_false_elim "SimpFalseElim"
      else
        mk_tracer ctxt Slam_Common.trace_msg_false_elim "FalseElim"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val () = tracer (fn () =>
      "start: " ^ JClause.pretty_clause ctxt c ^ ", subterm: " ^ @{make_string} (lp, cp))
    val (s, s', b) = JClause.lit_at cp c |> JLit.orient lp |> JLit.dest
    val unifiers =
      if not b then fail Seq.empty (K "not a positive literal") else
      if as_simplification
        then if s aconv @{term "False"} andalso s' aconv @{term "True"}
          then Seq.single (Envir.empty (JClause.maxidx c))
          else
            fail Seq.empty (K "\<sigma> is not the identity")
      else
        Slam_Unify.smash_unifiers
          (Context.Proof ctxt)
          [(s, @{term "False"}), (s', @{term "True"})]
          (Envir.empty (JClause.maxidx c))
    val (unifiers, _) = Seq.chop (Slam_Common.get_unifier_cutoff ctxt) unifiers
    fun build_conclusion unifier =
      let
        val () = tracer (fn () => "build_conclusion")
        val c = c |> JClause.norm_beta_eta_qeta_env ctxt unifier |> JClause.recompute_selected ctxt
        val origin =
          if as_simplification
            then
              Slam_Log.SimpFalseElim
                { premise = JClause.id c, literal = (lp, cp), substitution = unifier }
            else
              Slam_Log.FalseElim
                { premise = JClause.id c, literal = (lp, cp), substitution = unifier }
      in
        if not as_simplification andalso not (JClause.is_eligible_cpos c (cp, eligibility)) then
          fail NONE (K "literal not eligible") else (* 2. *)
        c
        |> JClause.delete_lit_at ctxt cp
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ctxt ()
        |> JClause.set_origin ctxt origin
        |> trace_concl ctxt tracer
        |> SOME
      end
  in
    map_filter build_conclusion unifiers
  end

val infer_false_elim = impl_simp_infer_false_elim false

val simp_false_elim = impl_simp_infer_false_elim true

fun bool_rw_non_var_rules include_iff_as_equal =
  let
    val truth_values = [@{term "True"}, @{term "False"}]
    val truth_value_pairs = Slam_Common.cartesian_product truth_values truth_values
    fun ml_conj (x, y) = x andalso y
    fun ml_disj (x, y) = x orelse y
    fun ml_imp (x, y) = (not x) orelse y
    fun make_binary_truth_table (logical_constructor, ml_function) =
      map
        (fn pair =>
          (logical_constructor pair, (hol_bool_of o ml_function o apply2 ml_bool_of) pair))
        truth_value_pairs
  in
    [ (@{term "\<not> True"}, @{term "False"})
    , (@{term "\<not> False"}, @{term "True"}) ]
    @
    maps make_binary_truth_table
      (
        [ (HOLogic.mk_conj, ml_conj)
        , (HOLogic.mk_disj, ml_disj)
        , (HOLogic.mk_imp, ml_imp) ]
        (* Note: this is not specified in the paper *)
        (* Note: the not equal case is not required, because the inner equality can be handled
        first, and the negation rule above applies *)
        @
        (if include_iff_as_equal then [(HOLogic.mk_eq, op=)] else [])
      )

  end

(* FIXME: o\<lambda>Sup: "[...] oSup relies heavily on BoolSimp, and we keep this rule as the basis of our
Boolean simplification machinery [...] BoolRw can be reduced to two cases [...]"
We should probably do the same, see zipperposition/booleans.ML:1072 (simplify_bools), in particular
to get the boolean implication simplifications from oSup. (Note oSup: "assuming \<not> is not greater
than \<longrightarrow>") *)
(* Implementation of BoolRw, EqHoist, NeqHoist, ForallHoist and ExistsHoist.
unifies u with boolean pattern, returns C<\<top>> or C<\<bottom>> and checks relevant conditions *)
(* WARNING: Do not change disjunct_with, except for applying the appropriate unifier to it (i.e. no
changing of maxidx). Proof reconstruction for \<forall>- and \<exists>Hoist relies on knowing the exact indexname of
the variable x occuring in disjunct_with. *)
fun impl_infer_bool_rw_eq_neq_fa_ex_hoist
  ctxt
  (tracer : (unit -> string) -> unit)
  (c : JClause.T, u_pos : JClause.full_pos, eligibility)
  (pattern : term)
  (u_var_allowed : bool) (* this is false for BoolRw but true for the others *)
  (insert_for_u : term) (* will be \<top> or \<bottom> *)
  (disjunct_with : JLit.T option) (* this is needed for the Hoist rules *)
  : (Envir.env * JClause.T) list
=
  let
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val u = JClause.subterm_at_full_pos c u_pos
    val () = tracer (fn () => "u = " ^ Slam_Common.pretty_term ctxt u)
  in
  if (not u_var_allowed) andalso (is_Var u) then (* BoolRw: 2. *) fail [] (K "u is a variable") else
  let
    val maxidx =
      Int.max
        ( Int.max (JClause.maxidx c, maxidx_of_term pattern)
        , the_default ~1 (Slam_Common.map_some JLit.maxidx_of disjunct_with) )
    val u_at_toplevel_and_eq_to_bool_or_eq_to_var_headed_term =
      case u_pos of
        ([], lpos, cpos) =>
          let
            val (_, other_side, is_positive) =
              c |> JClause.lit_at cpos |> JLit.orient lpos |> JLit.dest
          in
            is_positive andalso
              (other_side = @{term True}
                orelse other_side = @{term False}
                orelse JTerm.is_variable_headed other_side)
          end
      | _ => false
    val u_variable_headed_condition =
      not (JTerm.is_variable_headed u)
        orelse u_at_toplevel_and_eq_to_bool_or_eq_to_var_headed_term
    val unifiers =
      Slam_Unify.smash_unifiers
        (Context.Proof ctxt)
        [(u, pattern)]
        (Envir.empty (maxidx + 1))
    val (unifiers, _) = Seq.chop (Slam_Common.get_unifier_cutoff ctxt) unifiers
    fun build_conclusion unifier =
      let
        val () = tracer (fn () => "build_conclusion")
        val c =
          c
          |> JClause.norm_beta_eta_qeta_env ctxt unifier
          |> JClause.recompute_selected ctxt
        val new_literal =
          Slam_Common.map_some
            (JLit.norm_beta_eta_qeta_env unifier)
            disjunct_with
        val insert_for_u = JTerm.norm_beta_eta_qeta_env unifier insert_for_u

        (* FIXME: remove after debugging *)
        val u_subbed = JClause.subterm_at_full_pos c u_pos
        val _ = if type_of u_subbed <> type_of insert_for_u then
            (writeln ("TYPES DONT MATCH: " ^ Slam_Common.pretty_term ctxt u_subbed ^ " <> " ^ Slam_Common.pretty_term ctxt insert_for_u);
            writeln ("NORMED CLAUSE: " ^ JClause.pretty_clause ctxt c);
            writeln ("PATTERN: " ^ Slam_Common.pretty_term ctxt pattern);
            writeln ("U: " ^ Slam_Common.pretty_term ctxt u);
            writeln ("UNIFIER: " ^ Slam_Common.pretty_tenv ctxt (Envir.term_env unifier));
            writeln ("INSERT FOR U:" ^ Slam_Common.pretty_term ctxt insert_for_u);
            error "TYPESDONTMATCH")
          else ()

        val maxidx =
          Int.max
            ( Int.max (JClause.maxidx c, maxidx_of_term insert_for_u)
            , the_default ~1 (Slam_Common.map_some JLit.maxidx_of new_literal) )
      in
        (* 3. the position of u is eligible in C w.r.t. \<sigma> *)
        if not (JClause.is_eligible_full_pos c (u_pos, eligibility)) then
          fail NONE (K "the position of u is not eligible") else
        (* 4. if the head of u is a variable ... *)
        if not u_variable_headed_condition then
          fail NONE (K ("u is variable headed but isn't applied or the affected literal is not of "
            ^ "the form u\<approx>\<top>, u\<approx>\<bottom>, or u\<approx>v with v variable-headed")) else
        c
        |> JClause.map_at_full_pos u_pos (K insert_for_u)
        |> JClause.set_maxidx maxidx
        (* add the new literal if it exists, otherwise apply identity function *)
        |> the_default I (Slam_Common.map_some (JClause.add_literal ctxt) new_literal)
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ctxt ()
        |> pair unifier
        |> SOME
      end
    val result = map_filter build_conclusion unifiers
    val () = tracer (fn () => "done")
  in
    result
  end
  end

val bool_simp_var_lemmas =
  [
    @{lemma "\<And>b. (\<not>\<not>b) = b" by auto}
    (* Leo-III simp, see section 4.2.1 of Extensional Paramodulation for Higher-Order Logic and its
    Effective Implementation Leo-III *)
  , @{lemma "\<And>b. (b \<or> b) = b" by auto}
  , @{lemma "\<And>b. (b \<and> b) = b" by auto}
  , @{lemma "\<And>b. (\<not>b \<or> b) = True" by auto}
  , @{lemma "\<And>b. (b \<or> \<not>b) = True" by auto}
  , @{lemma "\<And>b. (\<not>b \<and> b) = False" by auto}
  , @{lemma "\<And>b. (b \<and> \<not>b) = False" by auto}
  , @{lemma "\<And>b. (b \<or> True) = True" by auto}
  , @{lemma "\<And>b. (True \<or> b) = True" by auto}
  , @{lemma "\<And>b. (b \<and> True) = b" by auto}
  , @{lemma "\<And>b. (True \<and> b) = b" by auto}
  , @{lemma "\<And>b. (b \<or> False) = b" by auto}
  , @{lemma "\<And>b. (False \<or> b) = b" by auto}
  , @{lemma "\<And>b. (b \<and> False) = False" by auto}
  , @{lemma "\<And>b. (False \<and> b) = False" by auto}
  , @{lemma "\<And>t. (t = t) = True" by auto}
  , @{lemma "\<And>t. (t \<noteq> t) = False" by auto}
  , @{lemma "\<And>b. (b = True) = b" by auto}
  , @{lemma "\<And>b. (True = b) = b" by auto}
  , @{lemma "\<And>b. (b = False) = (\<not> b)" by auto}
  , @{lemma "\<And>b. (False = b) = (\<not> b)" by auto}
    (* BoolSimp, Superposition with First-Class Booleans and Inprocessing Clausification *)
  , @{lemma "\<And>b. (True \<longrightarrow> b) = b" by auto}
  , @{lemma "\<And>b. (False \<longrightarrow> b) = True" by auto}
  , @{lemma "\<And>b. (b \<longrightarrow> False) = (\<not> b)" by auto}
  , @{lemma "\<And>b. (b \<longrightarrow> \<not> b) = (\<not> b)" by auto}
  , @{lemma "\<And>b. (\<not> b \<longrightarrow> b) = b" by auto}
  , @{lemma "\<And>b. (b \<longrightarrow> b) = True" by auto}
  (* Computing Small Clause Normal Forms *)
  (* FIXME: evaluate performance *)
  , @{lemma "\<And>P. (\<forall>x. P) = P" by auto}
  , @{lemma "\<And>P. (\<exists>x. P) = P" by auto}
  , @{lemma "\<And>s t. (if True then s else t) = s" by auto}
  , @{lemma "\<And>s t. (if False then s else t) = t" by auto}
  , @{lemma "\<And>b s. (if b then s else s) = s" by auto}
  ]

fun split_bool_simp_rule th =
  th
  |> Thm.prop_of
  |> HOLogic.dest_Trueprop
  |> HOLogic.dest_eq

val bool_simp_rules =
  bool_rw_non_var_rules true @ map split_bool_simp_rule bool_simp_var_lemmas

val bool_simp_rules_index =
  Top_Symbol_Index.empty
  |> fold (fn (lhs, rhs) => Top_Symbol_Index.insert_term (lhs, (lhs, rhs))) bool_simp_rules

(* FIXME: duplication with impl_infer_bool_rw_eq_neq_fa_ex_hoist *)
fun impl_simp_bool_rw
  ctxt
  (tracer : (unit -> string) -> unit)
  (c : JClause.T, u_pos : JClause.full_pos, eligibility)
  (pattern : term)
  (rhs : term)
  : ((term * term) * (Envir.env * JClause.T)) option
=
  let
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val u = JClause.subterm_at_full_pos c u_pos
    val () = tracer (fn () => "u = " ^ Slam_Common.pretty_term ctxt u)
  in
  if is_Var u then (* BoolRw: 2. *) fail NONE (K "u is a variable") else
  let
    val (pattern, rhs) = apply2 (Logic.incr_indexes ([], (JClause.maxidx c + 1))) (pattern, rhs)
    val maxidx = Int.max (JClause.maxidx c, maxidx_of_term pattern)
    val matchers =
      Slam_Unify.matchers
        (Context.Proof ctxt)
        (maxidx + 1)
        [(pattern, u)]
    val maybe_matcher: Envir.env option = Option.map #1 (Seq.pull matchers)
    fun build_conclusion matcher =
      let
        val () = tracer (fn () => "build_conclusion")
        val c =
          c
          |> JClause.norm_beta_eta_qeta_env ctxt matcher 
          |> JClause.recompute_selected ctxt
        val insert_for_u = JTerm.norm_beta_eta_qeta_env matcher rhs

        val maxidx = Int.max (JClause.maxidx c, maxidx_of_term insert_for_u)
      in
        c
        |> JClause.map_at_full_pos u_pos (K insert_for_u)
        |> JClause.set_maxidx maxidx
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ctxt ()
        |> pair matcher
        |> pair (pattern, rhs)
        |> SOME
      end
    val result = Option.mapPartial build_conclusion maybe_matcher
    val () = tracer (fn () => ("done"))
  in
    result
  end
  end

(*
fun simp_bool_rw ctxt (c, u_pos, eligibility) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_simp_bool_rw "SimpBoolRw"
    val () = tracer (fn () => "start: " ^ JClause.pretty_clause ctxt c ^ ", subterm: " ^ @{make_string} u_pos)
    val maxidx = JClause.maxidx c
    val rw_rules =
      (* [ (fresh_variable_eq_itself, @{term "True"})
      , (HOLogic.mk_not fresh_variable_eq_itself, @{term "False"}) ]
      @ *)
      bool_rw_non_var_rules true
      @
      map split_bool_simp_rule bool_simp_rules
    fun apply_rw_rule (t, t') =
      let val () = tracer (fn () =>
        "rule " ^ Slam_Common.pretty_term ctxt t ^ " \<mapsto> " ^ Slam_Common.pretty_term ctxt t')
      in
        impl_simp_bool_rw ctxt tracer (c, u_pos, eligibility) t t'
        |> Option.map (fn (unifier, clause) =>
          clause
          |> JClause.set_origin ctxt
            (Slam_Log.SimpBoolRw
              { premise = JClause.id c, subterm = u_pos, subrule = (t, t'), substitution = unifier })
          |> trace_concl ctxt tracer
          )
      end
  in
    filter_map apply_rw_rule rw_rules
  end
*)

fun bool_simp 
  ctxt
  clause
  : { clause : JClause.T, archive : JClause.T list }
=
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_bool_simp "BoolSimp"
    val () = tracer (fn () => "start: " ^ JClause.pretty_clause ctxt clause)
    fun simp_subterm fp c : ((term * term) * (Envir.env * JClause.T)) option =
      (* invariant: fp is a valid green full pos for c *)
      let
        val subterm: term = JClause.subterm_at_full_pos c fp
      in
        Top_Symbol_Index.get_first_of_generalizations
          subterm
          bool_simp_rules_index
          ( fn (lhs, rhs) =>
              impl_simp_bool_rw ctxt tracer (c, fp, JClause.Unknown) lhs rhs
          )
      end
    fun repeat_simp_subterm countdown fp (state as { clause, archive }) =
      if countdown < 0
        then
          ( warning "bool_simp: more than 10 simplification steps in subterm";
            { clause = clause, archive = archive }
          )
        else
          case simp_subterm fp clause of
            NONE => state
          | SOME ((lhs, rhs), (matcher, rewritten_clause)) =>
              let
                val rewritten_clause =
                  rewritten_clause
                  |> JClause.set_origin ctxt
                    (Slam_Log.SimpBoolRw
                      { premise = JClause.id clause, subterm = fp, subrule = (lhs, rhs), substitution = matcher })
              in
                repeat_simp_subterm
                  (countdown - 1)
                  fp
                  { clause = rewritten_clause, archive = clause :: archive }
              end
    fun fold_postorder_over_green_full_pos (f : JClause.full_pos -> 'a -> 'a) : JClause.T -> 'a -> 'a =
      JClause.fold_postorder_with_green_full_pos (fn fp => fn _ => f fp)
  in
    fold_postorder_over_green_full_pos
      (repeat_simp_subterm 10)
      clause
      { clause = clause, archive = [] }
  end

(* FIXME: Idea: have the rw rules as active clauses, then this is basically superposition *)
fun infer_bool_rw ctxt (c, u_pos, eligibility) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_bool_rw "BoolRw"
    val () = tracer (fn () => "start: " ^ JClause.pretty_clause ctxt c ^ ", subterm: " ^ @{make_string} u_pos)
    val maxidx = JClause.maxidx c
    (* FIXME: move renaming into impl_simp_bool_rw... ? *)
    val fresh_typ = TVar (("'a", maxidx + 1), Sign.defaultS (Proof_Context.theory_of ctxt)) (* type of y FIXME: better name? *)
    val fresh_variable = Var (("y_brw", maxidx + 1), fresh_typ) (* y *)
    val fresh_variable_eq_itself = HOLogic.mk_eq (fresh_variable, fresh_variable)
    val rw_rules =
      [ (fresh_variable_eq_itself, @{term "True"})
      , (HOLogic.mk_not fresh_variable_eq_itself, @{term "False"}) ]
      @
      bool_rw_non_var_rules false
    fun apply_rw_rule (t, t') =
      let val () = tracer (fn () =>
        "rule " ^ Slam_Common.pretty_term ctxt t ^ " \<mapsto> " ^ Slam_Common.pretty_term ctxt t')
      in
        impl_infer_bool_rw_eq_neq_fa_ex_hoist ctxt tracer (c, u_pos, eligibility) t false t' NONE
        |> map (fn (unifier, clause) =>
          clause
          |> JClause.set_origin ctxt
            (Slam_Log.BoolRw
              { premise = JClause.id c, subterm = u_pos, subrule = (t, t'), substitution = unifier })
          |> trace_concl ctxt tracer
          )
      end
  in
    maps apply_rw_rule rw_rules
  end

datatype HoistType = Eq | Neq | Forall | Exists

fun impl_eq_neq_hoist positive ctxt (c, u_pos, eligibility) =
  let
    val tracer =
      if positive
        then mk_tracer ctxt Slam_Common.trace_msg_eq_hoist "EqHoist"
        else mk_tracer ctxt Slam_Common.trace_msg_neq_hoist "NeqHoist"
    val () = tracer (fn () =>
      "start: " ^ JClause.pretty_clause ctxt c ^ ", subterm: " ^ @{make_string} u_pos)
    val maxidx = JClause.maxidx c
    val fresh_typ = TVar (("'a", maxidx + 1), Sign.defaultS (Proof_Context.theory_of ctxt)) (* type of y FIXME: better name? *)
    val fresh_x = Var (("x", maxidx + 1), fresh_typ) (* x *)
    val fresh_y = Var (("y_eqneqhoist", maxidx + 1), fresh_typ) (* y *)
    val x_eq_y_lit = JLit.mk (fresh_x, fresh_y, true)
    val pattern =
      (fresh_x, fresh_y)
      |> HOLogic.mk_eq
      |> not positive ? HOLogic.mk_not
    val insert_for_u = hol_bool_of (not positive)
  in
    impl_infer_bool_rw_eq_neq_fa_ex_hoist ctxt tracer (c, u_pos, eligibility) pattern true insert_for_u (SOME x_eq_y_lit)
    |> map (fn (unifier, clause) =>
      clause
      |> JClause.set_origin ctxt
        ((if positive then Slam_Log.EqHoist else Slam_Log.NeqHoist)
          { premise = JClause.id c, subterm = u_pos, substitution = unifier })
      |> trace_concl ctxt tracer
    )
  end

val infer_eq_hoist = impl_eq_neq_hoist true

val infer_neq_hoist = impl_eq_neq_hoist false

fun impl_forall_exists_hoist is_forall ctxt (c, u_pos, eligibility) =
  let
    val tracer =
      if is_forall
        then mk_tracer ctxt Slam_Common.trace_msg_forall_hoist "ForallHoist"
        else mk_tracer ctxt Slam_Common.trace_msg_exists_hoist "ExistsHoist"
    val () = tracer (fn () => "start: " ^ JClause.pretty_clause ctxt c ^ ", subterm: " ^ @{make_string} u_pos)
    val maxidx = JClause.maxidx c
    val fresh_typ =
      TVar (("'fresh_x_typ", maxidx + 1), Sign.defaultS (Proof_Context.theory_of ctxt))
    (* FIXME: use variable name from the quantifiers Abs. *)
    val fresh_x = Var (("x", maxidx + 1), fresh_typ)
    val fresh_predicate = Var (("y_faexhoist", maxidx + 1), fresh_typ --> @{typ bool})

    val quantifier =
      (if is_forall then HOLogic.all_const else HOLogic.exists_const) fresh_typ
    (* \<forall> y / \<exists> y*)
    val pattern = quantifier $ fresh_predicate
    (* y x = T / y x = \<bottom>*)
    val new_lit = JLit.mk (fresh_predicate $ fresh_x, hol_bool_of is_forall, true)
    (* \<top> / \<bottom> *)
    val insert_for_u = hol_bool_of (not is_forall)
  in
    impl_infer_bool_rw_eq_neq_fa_ex_hoist ctxt tracer (c, u_pos, eligibility) pattern true insert_for_u (SOME new_lit)
    |> map (fn (unifier, clause) =>
        clause
        |> JClause.set_origin ctxt
          ((if is_forall then Slam_Log.ForallHoist else Slam_Log.ExistsHoist)
            { premise = JClause.id c, subterm = u_pos, substitution = unifier, fresh_x = fresh_x })
        |> trace_concl ctxt tracer
    )
  end

val infer_forall_hoist = impl_forall_exists_hoist true

val infer_exists_hoist = impl_forall_exists_hoist false

(* impl_infer_bool_rw_eq_neq_fa_ex_hoist ctxt clause u_pos pattern insert_for_u *)
fun impl_fa_ex_rw
  is_forall
  ctxt
  (c : JClause.T, u_pos : JClause.full_pos, eligibility)
  : JClause.T list
=
  let
    val tracer =
      if is_forall
        then mk_tracer ctxt Slam_Common.trace_msg_forall_rw "ForallRw"
        else mk_tracer ctxt Slam_Common.trace_msg_exists_rw "ExistsRw"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val () = tracer (fn () => "start: " ^ JClause.pretty_clause ctxt c ^ ", subterm: " ^ @{make_string} u_pos)
  in
  (* condition 5. *)
  if
      (case u_pos of
        ([], lpos, cpos) =>
          let
            val (_, other_side, is_positive) =
              c |> JClause.lit_at cpos |> JLit.orient lpos |> JLit.dest
          in
            if is_positive andalso is_forall andalso other_side = @{term True} then true else
            if is_positive andalso not is_forall andalso other_side = @{term False} then true else
            false (* don't fail *)
          end
        | _ => false)
    then fail [] (K ("literal is of the form " ^ (if is_forall then "u\<approx>\<bottom>" else "u\<approx>\<top>"))) else
  let val u = JClause.subterm_at_full_pos c u_pos
      val () = tracer (fn () => "u = " ^ Slam_Common.pretty_term ctxt u)
  in
  if is_Var u then fail [] (K "u is a variable") (* 2 *) else
  let
    (* from outer *)
    val maxidx = JClause.maxidx c
    val fresh_typ = TVar (("'b", maxidx + 1), Sign.defaultS (Proof_Context.theory_of ctxt)) (* \<beta> *)
    val fresh_predicate = Var (("y_faexrw", maxidx + 1), fresh_typ --> @{typ bool})
    val quantifier =
      (if is_forall then HOLogic.all_const else HOLogic.exists_const) fresh_typ
    (* \<forall> ?y / \<exists> ?y *)
    val pattern = quantifier $ fresh_predicate

    val maxidx = Int.max (JClause.maxidx c, maxidx_of_term pattern)
    val u_at_toplevel_and_eq_to_bool_or_eq_to_var_headed_term =
      case u_pos of
        ([], lpos, cpos) =>
          let
            val (_, other_side, is_positive) =
              c |> JClause.lit_at cpos |> JLit.orient lpos |> JLit.dest
          in
            is_positive andalso
              (other_side = @{term True}
                orelse other_side = @{term False}
                orelse JTerm.is_variable_headed other_side)
          end
      | _ => false
    val u_variable_headed_condition =
      not (JTerm.is_variable_headed u)
        orelse u_at_toplevel_and_eq_to_bool_or_eq_to_var_headed_term
    val unifiers =
      Slam_Unify.smash_unifiers
        (Context.Proof ctxt)
        [(u, pattern)]
        (Envir.empty (maxidx + 1))
    val (unifiers, _) = Seq.chop (Slam_Common.get_unifier_cutoff ctxt) unifiers
    fun build_conclusion unifier =
      let
        val () = tracer (fn () => "build_conclusion")
        val c =
          c
          |> JClause.norm_beta_eta_qeta_env ctxt unifier
          |> JClause.recompute_selected ctxt

        val abstract_over = Free ("implfaexrwabsvar002460177", fresh_typ)
        val () = if (not (exists_subterm (fn Free (name, _) =>
          name = #1 (dest_Free abstract_over) | _ => false) fresh_predicate)) then () else error "impl_fa_ex_rw: assertion failed"
        val choice_body = (is_forall ? HOLogic.mk_not) (fresh_predicate $ abstract_over)
        val choice_witness =
          JTerm.make_choice_witness abstract_over choice_body
          (* critical *)
          |> JTerm.norm_beta_eta_qeta_env unifier
        (* Note: FV(?y\<sigma>) = FV((SOME z. ?y z)\<sigma>), where FV gives the set of *schematic* variables *)
        val { skolem_constant, skolem_constant_with_args, skolem_constant_definition } =
          JTerm.make_skolem_constant choice_witness

        (* Note: ?y\<sigma> (sk TYPE(\<dots>) x\<^sub>1 \<dots>) is not equal to (?y (sk TYPE(\<dots>) x\<^sub>1 \<dots>)) \<sigma>, because \<sigma> can
        assign the x\<^sub>i, since \<sigma> \<in> CSU(Q. ?y, u) *)
        val insert_for_u =
          JTerm.norm_beta_eta_qeta_env unifier (fresh_predicate $ skolem_constant_with_args)

        val maxidx = Int.max (JClause.maxidx c, maxidx_of_term insert_for_u)
      in
        (* 3. the position of u is eligible in C w.r.t. \<sigma> *)
        if not (JClause.is_eligible_full_pos c (u_pos, eligibility)) then fail NONE (K "u is not eligible") else
        (* 4. if the head of u is a variable ... *)
        if not u_variable_headed_condition then fail NONE (K "the head of us is a variable") else
        c
        |> JClause.map_at_full_pos u_pos (K insert_for_u)
        |> JClause.set_maxidx maxidx
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ctxt ()
        |> JClause.set_origin ctxt (
          (if is_forall then Slam_Log.ForallRw else Slam_Log.ExistsRw)
            { premise = JClause.id c
            , subterm = u_pos
            , substitution = unifier
            , skolems =
                [(skolem_constant, skolem_constant_with_args, skolem_constant_definition)]
            })
        |> trace_concl ctxt tracer
        |> SOME
      end
  in
    map_filter build_conclusion unifiers
  end
  end
  end

fun impl_infer_forall_exists_rw is_forall ctxt (clause, u_pos, eligibility) =
  (let

    val () = ()
    (* val _ = writeln ("FaExRw past more with u_pos" ^ @{make_string} u_pos ) *)
  in
      impl_fa_ex_rw is_forall ctxt (clause, u_pos, eligibility)
  end)

val infer_forall_rw = impl_infer_forall_exists_rw true

val infer_exists_rw = impl_infer_forall_exists_rw false

(* C \<or> s                      \<noteq> s'                              *)
(* ------------------------------------------------------ NegExt *)
(* C \<or> s (SOME x. s x \<noteq> s' x) \<noteq> s' (SOME x. s x \<noteq> s' x)        *)
fun infer_neg_ext ctxt (c, cpos, eligibility) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_neg_ext "NegExt"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val () = tracer (fn () => "start: " ^ JClause.pretty_clause ctxt c ^ ", literal: " ^ @{make_string} cpos)
  in
  if not (JClause.is_eligible_cpos c (cpos, eligibility)) then fail [] (K "literal not eligible") else
  let val lit = JClause.lit_at cpos c in
  if JLit.is_positive lit then fail [] (K "not a negative literal") else
  let val (s, s', false) = JLit.dest lit in
  if null (Term.binder_types (fastype_of s)) then fail [] (K "not of function type") else
  let
    val x = Free ("x_neg_ext", domain_type (fastype_of s))
    val () = if (not (exists_subterm (fn Free (name, _) =>
      name = #1 (dest_Free x) | _ => false) s)) then () else error "infer_neg_ext: assertion 1 failed"
    val () = if (not (exists_subterm (fn Free (name, _) =>
      name = #1 (dest_Free x) | _ => false) s')) then () else error "infer_neg_ext: assertion 2 failed"
    val choice_body = HOLogic.mk_not (HOLogic.mk_eq (s $ x, s' $ x))
    (* Note: FV(s\<noteq>s') = FV(SOME z. s z \<noteq> s' z), where FV gives the set of *schematic* variables. *)
    val choice_witness = JTerm.make_choice_witness x choice_body
    val { skolem_constant, skolem_constant_with_args, skolem_constant_definition } =
      JTerm.make_skolem_constant choice_witness

    val new_literal = JLit.mk (s $ skolem_constant_with_args, s' $ skolem_constant_with_args, false)

    val new_clause =
      c
      |> JClause.map_at_cpos cpos (K new_literal)
      |> JClause.norm_beta_eta_qeta ctxt
      |> JClause.norm_negative_predicate_literals ctxt
      |> JClause.recompute_selected ctxt
      |> JClause.set_maxidx (JClause.maxidx c)
      |> JClause.refresh_id ctxt ()
      |> JClause.set_origin ctxt
          (Slam_Log.NegExt
            { premise = JClause.id c
            , literal = cpos
            , skolems = [(skolem_constant, skolem_constant_with_args, skolem_constant_definition)]
            })
      |> trace_concl ctxt tracer
  in
    [new_clause]
  end end end end

(* FIXME: maximal context *)
(* C \<or> f t\<^sub>1 \<dots> t\<^sub>n \<noteq> f s\<^sub>1 \<dots> s\<^sub>n *)
(* --------------------------- *)
(* C \<or> t\<^sub>n \<noteq> s\<^sub>n \<or> \<dots> \<or> t\<^sub>1 \<noteq> s\<^sub>1 *)
fun infer_neg_cong_fun ctxt (c, cpos, eligibility) =
  let
    val tracer = mk_tracer ctxt Slam_Common.trace_msg_neg_cong_fun "NegCongFun"
    fun fail failure_value msg = (tracer (fn () => "fail: " ^ msg ()); failure_value)
    val () = tracer (fn () => "start: " ^ JClause.pretty_clause ctxt c ^ ", literal: " ^ @{make_string} cpos)
  in
  if not (JClause.is_eligible_cpos c (cpos, eligibility)) then fail [] (K "literal not eligible") else
  let val lit = JClause.lit_at cpos c in
  if JLit.is_positive lit then fail [] (K "not a negative literal") else
  let
    val (f_ss, g_ts, false) = JLit.dest lit
    val ((f, ss), (g, ts)) = apply2 strip_comb (f_ss, g_ts)
  in
  if not (f aconv g) then fail [] (K "unequal heads") else
  let val () = if (length ss = length ts) then () else error "infer_neg_cong_fun: assertion failed" in
  if not (exists JTerm.has_functional_type ss) then fail [] (K "no argument has functional type") else
  let
    val disj_pairs = map (uncurry JLit.mk_neq) (ss ~~ ts)
  in
    c
    |> JClause.delete_lit_at ctxt cpos
    |> fold (JClause.add_literal ctxt) disj_pairs
    |> JClause.norm_beta_eta_qeta ctxt
    |> JClause.norm_negative_predicate_literals ctxt
    |> JClause.recompute_selected ctxt
    |> JClause.set_maxidx (JClause.maxidx c)
    |> JClause.refresh_id ctxt ()
    |> JClause.set_origin ctxt
        (Slam_Log.NegCongFun
          { premise = JClause.id c
          , literal = cpos
          , number_of_new_lits = length disj_pairs
          })
    |> trace_concl ctxt tracer
    |> single
  end end end end end

(** Saturation Loop **)

(* FIXME: make sure to include given_clause itself in simplificatons unless it's redundant *)
fun forward_simplify
  ctxt
  { forward = forward, cheap = cheap }
  active
  unit_index
  green_index
  subsumption_index
  given_clause
=
  let
    val () = if (if cheap then (* also *) forward else true) then () else error "forward_simplify: assertion failed"
    (* tracing *)
    val do_trace =
      if forward then
        Config.get ctxt Slam_Common.trace_forward_simp
      else if cheap then
        Config.get ctxt Slam_Common.trace_cheap_simp
      else
        Config.get ctxt Slam_Common.trace_backward_simp
    val ctxt = Config.map Slam_Common.trace (fn s => s andalso do_trace) ctxt

    val active_units = Seq.filter JClause.is_unit (Seq.of_list (Slam_Clause_Set.dest active))
    val all_orientations : JClause.T Seq.seq -> (JClause.T * JLit.lpos) Seq.seq =
      fn cs => Slam_Common.seq_cartesian_product cs (Seq.of_list [JLit.Left, JLit.Right])

    (* rule configuration *)
    val all_disabled = Config.get ctxt Slam_Common.disable_all
    (* val _ = if all_disabled then writeln "ALL SIMPLIFICATIONS DISABLED!!!" else () *)
    fun if_cfg rule = if not all_disabled orelse Config.get ctxt rule then I else K Seq.empty

    fun simp_fun_of_seq clause_seq c =
      case Seq.pull (clause_seq c) of
        NONE => []
      | SOME (c, _) => [c]

    (* FIXME: remove active_units hack *)
    val simp_funs =
      let
        val simp_false_elim_rewrites: JClause.T -> JClause.T Seq.seq = fn c =>
          if_cfg Slam_Common.rule_simp_false_elim (
            let
              val clause_lit_sides =
                JClause.cposs_of c
                |> map (rpair JClause.Unknown)
                |> Slam_Common.cartesian_product [JLit.Left, JLit.Right]
                |> map (fn (lp, (cp, eligibility)) => (c, (lp, cp), eligibility))
            in
              Seq.of_list (maps (simp_false_elim ctxt) clause_lit_sides)
            end)

        (* FIXME rewrites is a misnomer inherited from rn_rp_rewrites *)
        val oc_rewrites : Slam_Simplify.simp_fun = fn c =>
          if_cfg Slam_Common.rule_simp_outer_claus (
          (Seq.map (pair c) (Seq.of_list (0 upto (length (JClause.literals c) - 1))))
          |> Seq.map (fn (c, cp) => (c, cp, JClause.Unknown))
          |> Seq.map (simp_bool_outer_claus ctxt)
          |> Seq.map_filter (fn cs => case cs of [] => NONE | _ => SOME cs)
          )
          |> Seq.pull
          |> Slam_Common.map_some fst
          |> the_default []
        val ps_rewrites : JClause.T -> JClause.T Seq.seq = fn c =>
          if_cfg Slam_Common.rule_positive_simplify_reflect (
            Slam_Common.seq_cartesian_product active_units
              (Seq.map (pair c) (Seq.of_list (0 upto (length (JClause.literals c) - 1))))
            |> Seq.map_filter (fn (unit, target) => simp_positive_simplify_reflect ctxt unit target)
          )
        val ns_rewrites : JClause.T -> JClause.T Seq.seq = fn c =>
          if_cfg Slam_Common.rule_negative_simplify_reflect (
            Slam_Common.seq_cartesian_product
              (all_orientations active_units)
              (Seq.map (pair c) (Seq.of_list (0 upto (length (JClause.literals c) - 1))))
            |> Seq.map_filter (fn (oriented_unit, target) =>
              simp_negative_simplify_reflect ctxt oriented_unit target)
          )
        val dd_dr_rewrites : JClause.T -> JClause.T Seq.seq = fn c =>
          Seq.map_filter
            (fn f => f c)
            (Seq.append
              (if_cfg
                Slam_Common.rule_delete_duplicated_lits
                (Seq.single (simp_delete_duplicated_lits ctxt)))
              (if_cfg
                Slam_Common.rule_delete_resolved_lits
                (Seq.single (simp_delete_resolved_lits ctxt))))
        val neg_ext_rewrites : JClause.T -> JClause.T Seq.seq = fn c =>
          if Config.get ctxt Slam_Common.neg_ext_as_simpl
            then
              if_cfg
                Slam_Common.rule_neg_ext (
                  Seq.of_list (
                    JClause.potentially_eligible_cposs_of c
                    |> map (fn (cp, eligibility) => (c, cp, eligibility))
                    |> maps (infer_neg_ext ctxt)
                  )
                )
            else Seq.empty
        val arg_cong_rewrites : JClause.T -> JClause.T Seq.seq = fn c =>
          if Config.get ctxt Slam_Common.arg_cong_as_simpl
            then
              if_cfg
                Slam_Common.rule_arg_cong (
                  Seq.of_list (
                    JClause.potentially_eligible_cposs_of c
                    |> map (fn (cp, eligibility) => (c, cp, eligibility))
                    |> maps (infer_arg_cong ctxt)
                  )
                )
            else Seq.empty
      in
        (* following Schulz: RN, RP, PS, NS, DD, DR *)
        (* [simp_fun_of_seq simp_bool_rewrites]
        @ *) [simp_fun_of_seq simp_false_elim_rewrites]
        @ [oc_rewrites]
        @ map simp_fun_of_seq
          ( (if not cheap then [ps_rewrites] else [])
          @ (if not cheap then [ns_rewrites] else [])
          @ [dd_dr_rewrites]
          @ [neg_ext_rewrites]
          @ [arg_cong_rewrites] )
      end

    (* FIXME: bool_simp and forward_rewrite should be part of the simplify fixed-point loop *)
    val { clause = given_clause, archive = bool_simp_archive } =
      if not all_disabled orelse Config.get ctxt Slam_Common.rule_bool_simp
        then bool_simp ctxt given_clause
        else { clause = given_clause, archive = [] }

    val { clause = given_clause, archive = rewriting_archive } =
      if forward
        then forward_rewrite_bottom_up ctxt active unit_index given_clause
        else { clause = given_clause, archive = [] }

    (* simplify until not possible anymore *)
    val (simplifications, archive) =
      Slam_Simplify.simplify
        false
        ctxt
        simp_funs
        given_clause
    val archive = archive @ rewriting_archive @ bool_simp_archive

    fun trace_msg_clauses tracer msg clauses =
      tracer ctxt
        (fn () => msg ^ JClause.pretty_clauses ctxt clauses)
    val _ = trace_msg_clauses Slam_Common.trace_msg "simplification results:" simplifications
    val _ = trace_msg_clauses Slam_Common.trace_msg_archive "intermediates " archive;
    (* val _ = Slam_Common.trace_msg ctxt (K "START REDUNDANCY CHECK") *)
    (* FIXME: return NONE/SOME instead of lists? *)
    fun discard_trivial clause =
      (* FIXME: this is not specified in the E paper, so should we perform inferences with
      tautologies?? *)
      (* NOTE: triviality check *should* to be done during or after cheap simplification *)
      if is_trivial clause orelse
          (not cheap andalso forward andalso
            is_forward_subsumed ctxt clause active subsumption_index) orelse
          (not cheap andalso is_equality_subsumed ctxt active given_clause)
        then
          let
            val _ =
              Slam_Common.trace_msg ctxt (fn () =>
                "discarding redundant or trivial clause" ^ JClause.pretty_clause ctxt clause)
          in
            []
          end
        else [clause]
  in
    (* FIXME: Rename "archive" to "intermediate" or "to_archive". *)
    { simplifications = flat (map discard_trivial simplifications), archive = archive }
  end

(* archive includes in particular deleted actives! *)
fun map_filter_partition ctxt f x (archive, changed) =
        case f x of
          (* NOTE: Discarding new_archive, since the active clause was deleted, and we don't need
          the simplification steps that led to deletion for proof reconstruction. *)
          { simplifications = [], archive = new_archive } =>
            (x :: archive, changed)
        | { simplifications = [y], archive = new_archive } =>
            (* One simplification, check the id to see if it is actually the original clause and no
            simplification was performed. *)
            if JClause.id y <> JClause.id x
              (* id changed, clause was simplified *)
              then (new_archive @ archive, y :: changed)
              (* clause was not simplified *)
              else
                if null new_archive
                  then (archive, changed)
                  (* error *)
                  else (
                    let
                      fun trace_msg_clauses tracer msg clauses =
                        tracer ctxt
                          (fn () => msg ^ JClause.pretty_clauses ctxt clauses)
                      val () =
                        trace_msg_clauses
                          Slam_Common.trace_msg_backward_simp
                          "active clause, single simplified active"
                          [x,y]
                      val () = Slam_Common.trace_msg_backward_simp ctxt (fn () =>
                        "with ids: "
                        ^ @{make_string} (JClause.id x)
                        ^ " and "
                        ^ @{make_string} (JClause.id y))
                      val () =
                        trace_msg_clauses
                          Slam_Common.trace_msg_archive
                          "intermediate simplificaitons"
                          new_archive
                    in
                      error ("map_filter_partition: clause id was unchanged, but intermediate " ^
                        "simplifications returned.")
                    end)
        (* This cannot happen in backwards simplification, because all the unary simplification
        rules (some of which have multiple conclusions) have been applied to active clauses already,
        so the only simplifications that apply are binary one between the active clause and the
        given clause. None of these yield multiple conclusions (this could change in the future). *)
        | ys => error ("map_filter_partition: multiple simplifications in backward " ^
            "simplification but there is no binary simplification with multiple conclusions!")

(* Returns a 3-tuple of:
* redundant actives and intermediate simplifications (for archival)
* simplified active clauses (to be added to the passive set after cheap simplification)
* unsimplifiable active clauses (to remain active)
*)
fun backward_simplify ctxt active unit_index green_index subsumption_index given_clause =
  let
    val active_ids = map JClause.id (Slam_Clause_Set.dest active) (* FIXME: remove together with assertion below *)

    (* tracing *)
    val do_trace = Config.get ctxt Slam_Common.trace_backward_simp
    val ctxt = Config.map Slam_Common.trace (fn s => s andalso do_trace) ctxt

    val archive = []
    val simplifications = []
    val { simplifications = rewrite_simplifications, archive = rewrite_archive } =
      backward_rewrite ctxt active green_index given_clause
    val archive = rewrite_archive @ archive
    val simplifications = rewrite_simplifications @ simplifications
    (* remove archived clauses from active set *)
    (* FIXME: remove deactivated clauses from indices? *)
    val active =
      active
      |> Slam_Clause_Set.delete_clauses simplifications
      |> Slam_Clause_Set.delete_clauses rewrite_archive
    val (new_archive, simplified_actives) =
      Slam_Clause_Set.fold
        (
          map_filter_partition
            ctxt
            (forward_simplify
              ctxt
              { forward = false, cheap = false }
              (Slam_Clause_Set.make [given_clause])
              unit_index
              green_index
              subsumption_index)
        )
      active
      ([], [])
    val simplified_actives = simplified_actives @ simplifications
    val unsimplifiable_actives = Slam_Clause_Set.delete_clauses (new_archive @ simplified_actives) active
    val archive = new_archive @ archive
    (* FIXME: at this point the active set and its indices are in an unusual state *)
    val subsumed_unsimplifiable_actives =
      get_backward_subsumed ctxt given_clause unsimplifiable_actives subsumption_index
    val unsimplifiable_actives = Slam_Clause_Set.delete_clauses subsumed_unsimplifiable_actives unsimplifiable_actives
    val archive = subsumed_unsimplifiable_actives @ archive
    val () = if (* FIXME remove *)
      (subset (op=) (active_ids, map JClause.id archive @ map JClause.id (Slam_Clause_Set.dest unsimplifiable_actives)))
      then ()
      else error "backward_simplify: assertion failed"
  in
    (archive, simplified_actives, unsimplifiable_actives)
  end

fun infer_clauses ctxt active given_clause green_index =
  let
    val active_list = Slam_Clause_Set.dest active
    (* the equality literals that are being eliminated *)
    val eqs_given : (JClause.T * (JLit.lpos * JClause.cpos)) list =
      map
        (pair given_clause)
        (Slam_Common.cartesian_product [JLit.Left, JLit.Right] (JClause.cposs_of given_clause))
    val eqs_active : (JClause.T * (JLit.lpos * JClause.cpos)) list =
      maps (fn c =>
          map (pair c) (Slam_Common.cartesian_product [JLit.Left, JLit.Right] (JClause.cposs_of c)))
        active_list
    (* what we're superposing into *)
    val targets_given : (JClause.T * JClause.full_pos) list =
      map (pair given_clause) (JClause.green_full_poss_of given_clause)
    val targets_active : (JClause.T * JClause.full_pos) list =
      maps (fn c => map (pair c) (JClause.green_full_poss_of c)) active_list
    val eq_target_pairs =
      Slam_Common.cartesian_product eqs_active targets_given
    (* for ERes, EFact, NegExt, NegCongFun *)
    val given_clause_cposs = JClause.cposs_of given_clause
    val given_clause_potentially_eligible_lits : (JClause.T * JClause.cpos * JClause.eligibility) list =
      JClause.potentially_eligible_cposs_of given_clause
      |> map (fn (cp, eligibility) => (given_clause, cp, eligibility))
    val given_clause_lpos_cpos_pairs =
      Slam_Common.cartesian_product [JLit.Left, JLit.Right] given_clause_cposs
    val given_clause_lit_sides = map (pair given_clause) given_clause_lpos_cpos_pairs
    val given_clause_potentially_eligible_lit_sides =
      JClause.potentially_eligible_cposs_of given_clause
      (* FIXME: optimize using JLit.kbo_compare_left_to_right *)
      |> Slam_Common.cartesian_product [JLit.Left, JLit.Right]
      |> map (fn (lp, (cp, eligibility)) => (given_clause, (lp, cp), eligibility))
    val given_clause_lpos_cpos_pairs_pairs =
      Slam_Common.cartesian_product
        given_clause_lpos_cpos_pairs
        given_clause_lpos_cpos_pairs
    val given_clause_terms = map (pair given_clause) (JClause.green_full_poss_of given_clause)
    val given_clause_potentially_eligible_terms =
      map (pair given_clause) (JClause.potentially_eligible_green_full_poss_of given_clause)
      |> map (fn (c, (fp, eligibility)) => (c, fp, eligibility))
    val all_disabled = Config.get ctxt Slam_Common.disable_all
    (* val _ = if all_disabled then writeln "ALL DISABLED!!!!" else () *)
    (* a bit contrived to make it lazy *)
    fun if_cfg rule f = if not all_disabled orelse Config.get ctxt rule then f () else []
    val rules =
    [ ( Slam_Common.rule_sup
      , Slam_Common.trace_sup
      , (fn _ => sup_given_into_active ctxt given_clause active green_index)
      )
    , ( Slam_Common.rule_sup
      , Slam_Common.trace_sup
      , (fn _ => sup_active_into_given ctxt given_clause active green_index)
      )
    (* ERes, EFact have already been performed for the active clauses *)
    , ( Slam_Common.rule_e_res
      , Slam_Common.trace_e_res
      , (fn _ => (maps (infer_eres ctxt) given_clause_potentially_eligible_lits))
      )
    , ( Slam_Common.rule_e_fact
      , Slam_Common.trace_e_fact
      , (fn _ => (maps (infer_efact ctxt given_clause) given_clause_lpos_cpos_pairs_pairs))
      )
    , ( Slam_Common.rule_arg_cong
      , Slam_Common.trace_arg_cong
      , (fn _ => if Config.get ctxt Slam_Common.arg_cong_as_simpl then [] else
          (maps (infer_arg_cong ctxt) given_clause_potentially_eligible_lits))
      )
    , ( Slam_Common.rule_neg_ext
      , Slam_Common.trace_neg_ext
      , (fn _ => if Config.get ctxt Slam_Common.neg_ext_as_simpl then [] else
          (maps (infer_neg_ext ctxt) given_clause_potentially_eligible_lits))
      )
    , ( Slam_Common.rule_neg_cong_fun
      , Slam_Common.trace_neg_cong_fun
      , (fn _ => (maps (infer_neg_cong_fun ctxt) given_clause_potentially_eligible_lits))
      )
    , ( Slam_Common.rule_bool_hoist
      , Slam_Common.trace_bool_hoist
      , (fn _ => (maps (infer_bool_hoist ctxt) given_clause_potentially_eligible_terms))
      )
    , ( Slam_Common.rule_false_elim
      , Slam_Common.trace_false_elim
      , (fn _ => (maps (infer_false_elim ctxt) given_clause_potentially_eligible_lit_sides))
      )
    , ( Slam_Common.rule_bool_rw
      , Slam_Common.trace_bool_rw
      , (fn _ => (maps (infer_bool_rw ctxt) given_clause_potentially_eligible_terms))
      )
    , ( Slam_Common.rule_eq_hoist
      , Slam_Common.trace_eq_hoist
      , (fn _ => (maps (infer_eq_hoist ctxt) given_clause_potentially_eligible_terms))
      )
    , ( Slam_Common.rule_neq_hoist
      , Slam_Common.trace_neq_hoist
      , (fn _ => (maps (infer_neq_hoist ctxt) given_clause_potentially_eligible_terms))
      )
    , ( Slam_Common.rule_forall_hoist
      , Slam_Common.trace_forall_hoist
      , (fn _ => (maps (infer_forall_hoist ctxt) given_clause_potentially_eligible_terms))
      )
    , ( Slam_Common.rule_exists_hoist
      , Slam_Common.trace_exists_hoist
      , (fn _ => (maps (infer_exists_hoist ctxt) given_clause_potentially_eligible_terms))
      )
    , ( Slam_Common.rule_forall_rw
      , Slam_Common.trace_forall_rw
      , (fn _ => (maps (infer_forall_rw ctxt) given_clause_potentially_eligible_terms))
      )
    , ( Slam_Common.rule_exists_rw
      , Slam_Common.trace_exists_rw
      , (fn _ => (maps (infer_exists_rw ctxt) given_clause_potentially_eligible_terms))
      )
    ]
  in
    maps (fn (cfg, trace, rule) => if_cfg cfg (Slam_Common.time_rule ctxt trace rule)) rules
  end

datatype step_result = Unsat | MaybeSat | Next

type prover_state =
  { context: Proof.context
  , countdown: int
  , passive: Slam_Passive_Set.T
  , active: Slam_Clause_Set.T
  , green_index: (int * JClause.full_pos) Term_Index.T
  , unit_index: (int * JLit.lpos) Term_Index.T
  , subsumption_index: Subsumption_Index.index
  , archive: JClause.T list
  }

fun given_clause_step
  { context, countdown, passive, green_index, unit_index, active, subsumption_index, archive }
=
  if countdown = 0 then error "TIMEOUT (increase slam_max_number_of_steps config option)" else
  (Runtime.exn_trace (fn () =>
  let
    (* tracing *)
    val _ = Slam_Common.trace_msg context (fn () => "countdown = " ^ @{make_string} countdown)
    fun trace_msg_clauses tracer msg clauses =
      tracer context
        (fn () => msg ^ JClause.pretty_clauses context clauses)
    val _ =
      let val passive_seq = passive |> Slam_Passive_Set.seq_of in
        Slam_Common.trace_msg_passive context (fn () => Slam_Passive_Set.pretty context 10 passive)
      end

    (* FIXME: return MAYBE_SAT (because of incompleteness) if passive set is empty (i.e. no
    inferences are possible and empty clause has not been derived). Later: no non-redundant
    inferences *)
    val (given_clause, passive) = Slam_Passive_Set.select_given_clause passive

    (* tracing *)
    val _ = trace_msg_clauses Slam_Common.trace_msg "given_clause " [given_clause]
  in
    (* simplify given_clause with active set *)
    case
      Slam_Common.time_and_trace
        (Slam_Common.trace_msg_forward_simp context)
        (fn () =>
          forward_simplify
            context
            { forward = true, cheap = false }
            active
            unit_index
            green_index
            subsumption_index
            given_clause
        )
        ()
    of
      (* given_clause redundant w.r.t. active set, don't add intermediat simplifications to archive *)
      { simplifications = [], archive = _ } =>
        ( Next
        , { context = context
          , countdown = countdown - 1
          , passive = passive
          , active = active
          , green_index = green_index
          , unit_index = unit_index
          , subsumption_index = subsumption_index
          , archive = archive } )
      (* select first simplification as given_clause *)
    | { simplifications = given_clause :: simplifications, archive = intermediate } =>
      (* if given_clause simplifies to (or is) [] then UNSAT *)
      case find_first JClause.is_false (given_clause :: simplifications) of
        SOME empty_clause =>
          ( Unsat
          , { context = context
            , countdown = countdown - 1
            , passive = passive
            , active = Slam_Clause_Set.add_new_clause empty_clause active
            , green_index = green_index
            , unit_index = unit_index
            , subsumption_index = subsumption_index
            , archive = intermediate @ archive } )
      | NONE =>
          let
            val archive = intermediate @ archive
            (* following zipperposition (src/prover/saturate.ml) add all simplifications except one
            (the current given_clause) to the passive set *)
            val passive = Slam_Passive_Set.add_new_clauses passive simplifications
            (* simplify actives with given clause *)
            (* FIXME: remove direct descendants of redundant_actives and simplified_actives from
            passive set, or: do what's described in the E 2.3 paper (deleting at activation time) *)
            val _ = Slam_Common.trace_msg_backward_simp context (K "START BACKWARD SIMPLIFICATION")
            val
              ( redundant_active_and_intermediate_simplifications
              , simplified_active
              , unsimplifiable_active )
            =
              Slam_Common.time_and_trace
                (Slam_Common.trace_msg_backward_simp context)
                (fn () =>
                  backward_simplify
                    context
                    active
                    unit_index
                    green_index
                    subsumption_index
                    given_clause
                )
              ()
            val archive = redundant_active_and_intermediate_simplifications @ archive
            (* remove simplified and redundant actives, add given_clause to active set *)
            val active = Slam_Clause_Set.add_new_clause given_clause unsimplifiable_active
            val green_index = Term_Index.insert_clause given_clause green_index
            val unit_index =
              if JClause.is_unit given_clause
                then Term_Index.insert_unit given_clause unit_index
                else unit_index
            val subsumption_index =
              Subsumption_Index.insert_clause given_clause subsumption_index
            (* perform all possible inferences between given_clause and active set NOTE: also
            computes inferences between given_clause and itself! *)
            val _ = Slam_Common.trace_msg_inferred context (K "START INFERRING NEW CLAUSES")
            val inferred_clauses = infer_clauses context active given_clause green_index
            val _ = trace_msg_clauses Slam_Common.trace_msg_inferred "inferred: " inferred_clauses
            (* clauses to be added to passive set *)
            val _ = Slam_Common.trace_msg_cheap_simp context (K "START CHEAP SIMPLIFICATION")
            val { simplifications = new_clauses, intermediate = cheap_simplification_intermediate } =
              fold
                (fn inferred_clause =>
                  fn { simplifications = simplifications, intermediate = intermediate } =>
                    let
                      val { simplifications = new_simplifications, archive = new_intermediate } =
                        (* cheap_simplify *)
                        Slam_Common.time_and_trace
                          (Slam_Common.trace_msg_cheap_simp context)
                          (fn () =>
                            forward_simplify
                              context
                              { forward = true, cheap = true }
                              active
                              unit_index
                              green_index
                              subsumption_index
                              inferred_clause
                          )
                        ()
                    in
                      (* FIXME: only add new_intermediate if simplifications non-empty. OR: just
                      move this logic into forward_simplify *)
                      { simplifications = new_simplifications @ simplifications
                      , intermediate = new_intermediate @ intermediate }
                    end
                )
              (simplified_active @ inferred_clauses)
              { simplifications = [], intermediate = []}
            val archive = cheap_simplification_intermediate @ archive
            val _ = trace_msg_clauses Slam_Common.trace_msg_cheap_simp "cheap_simplified: " new_clauses
            val _ = if length (filter (not o is_trivial) new_clauses) <> length new_clauses
              then error "assert failed: forward_simplify returned trivial clauses"
              else ()
            val _ = Slam_Common.trace_msg_cheap_simp context (K "END CHEAP SIMPLIFICATION")
            val _ = trace_msg_clauses Slam_Common.trace_msg_inferred "new_clauses: " new_clauses
            (* add inferred clauses to passive set *)
            val passive = Slam_Passive_Set.add_new_clauses passive new_clauses
            (* tracing *)
            val _ = trace_msg_clauses Slam_Common.trace_msg_active "active: " (Slam_Clause_Set.dest active)
          in
            ( Next
            , { context = context
              , countdown = countdown - 1
              , passive = passive
              , active = active
              , green_index = green_index
              , unit_index = unit_index
              , subsumption_index = subsumption_index
              , archive = archive } )
          end
  end
  ))

exception SLAM_EXCEPTION of exn * prover_state

fun given_clause_loop dump state =
  case (if dump
        then
          (case Exn.capture given_clause_step state of
            Exn.Exn e => raise (SLAM_EXCEPTION (e, state))
          | Exn.Res res => res)
        else given_clause_step state) of
    (Unsat, state) => (Unsat, state)
  | (Next, state) => given_clause_loop dump state

fun try_saturate context goal_term prems =
  let
    val _ = Slam_Common.trace_msg context (fn () =>
      "prems: "
      ^ Slam_Common.pretty_terms context
          (map (Object_Logic.drop_judgment context o Thm.prop_of) prems))

    (* "clausify" *)
    (* brittle, relies on Subgoal.FOCUS preserving order of prems *)
    val (axioms, negated_conjecture) = split_last prems
    fun clause_of_prem is_negated_conjecture prem =
      prem
      |> Thm.prop_of
      |> HOLogic.dest_Trueprop
      |> (fn t => JClause.of_term context (t, JClause_Id.new ()))
      |> JClause.set_origin context
        (if is_negated_conjecture andalso is_none goal_term
          then Slam_Log.NegatedConjecture { thm = prem }
          else Slam_Log.Axiom { thm = prem })
    val clauses = (map (clause_of_prem false) axioms) @ [clause_of_prem true negated_conjecture]
    val _ = Slam_Common.trace_msg context (fn () =>
      "clauses: "
      ^ Slam_Common.pretty_terms (Slam_Common.verbose_of context) (map JClause.term_of clauses))

    (* feature vector index *)
    val symbols = Subsumption_Index.collect_symbols clauses
    val () = Slam_Common.trace_msg context (fn () =>
      "Symbols for feature vector index:" ^ "\n" ^
      Slam_Common.pretty_terms (Slam_Common.verbose_of context) symbols)

    (* goal-oriented given-clause selection heuristic *)
    val goal_symbols =
      case goal_term of
        SOME goal_term =>
          Slam_Symbol_Table.add_symbols goal_term Slam_Symbol_Table.empty
      | NONE =>
          Slam_Symbol_Table.add_symbols (Thm.prop_of negated_conjecture) Slam_Symbol_Table.empty
    val () = Slam_Common.trace_msg context (fn () => "goal_symbols (for selection heuristic): "
        ^ Slam_Common.pretty_terms
            (Slam_Common.verbose_of context)
            (Slam_Symbol_Table.symbols goal_symbols))

    (* given clause loop *)
    val _ = Slam_Common.trace_msg context (fn () => "\n>>> start of given clause procedure <<<")
    val (result, final_state) =
      Runtime.exn_trace (fn () =>
        given_clause_loop
          true
          { context = context
          , countdown = Config.get context Slam_Common.max_number_of_steps
          , passive = Slam_Passive_Set.init goal_symbols clauses
          , active = Slam_Clause_Set.empty
          , green_index = Term_Index.empty
          , unit_index = Term_Index.empty
          , subsumption_index =
              Subsumption_Index.make_index symbols
          , archive = [] })
  in
    (result, final_state)
  end

fun make_clause_db state clause_id =
  case
    find_first (fn c => JClause.id c = clause_id) (Slam_Clause_Set.dest (#active state) @ (#archive state))
  of
    SOME clause => clause
  | NONE => error ("No clause with id " ^ @{make_string} clause_id ^ " in active set or archive.")

end;
