(*

general procedure:

1. Q\<^sub>\<approx> normalize
2. \<beta>\<eta>Q\<^sub>\<eta>-normalize
3. 

*)

signature JEHA =
sig
  val is_pos_unit : JClause.T -> bool
  val impl_simp_rewrite_lits : bool -> Proof.context -> JClause.T * JLit.lpos -> JClause.T * JClause.full_pos -> JClause.T option
  val find_single_green_disagreement : Proof.context -> term * term -> JTerm.tpos option
  val literal_can_match_single_disagreement : Proof.context -> int * JLit.T -> int * JLit.T -> (int * (JTerm.tpos * (JLit.lpos * Envir.env))) option
  val equality_subsumes : Proof.context -> JClause.T * JClause.T -> bool
  val bool_rw_non_var_rules : bool -> (term * term) list
  (* outer clausification *)
  val outer_clausify : Proof.context -> bool -> term -> JClause.T -> JClause.T list
  val is_trivial : JClause.T -> bool
  val is_equality_subsumed : Proof.context -> JClause.T list -> JClause.T -> bool
  val simp_bool_outer_claus : Proof.context -> JClause.T * JClause.cpos -> JClause.T list
  val simp_rewrite_positive_lits : Proof.context -> JClause.T * JLit.lpos -> JClause.T * JClause.full_pos -> JClause.T option
  val simp_rewrite_negative_lits : Proof.context -> JClause.T * JLit.lpos -> JClause.T * JClause.full_pos -> JClause.T option
  val simp_delete_resolved_lits : Proof.context -> JClause.T -> JClause.T option
  val simp_delete_duplicated_lits : Proof.context -> JClause.T -> JClause.T option
  val simp_bool_rw : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list 
  val infer_eq_neq_outer_claus : Proof.context -> JClause.T -> JClause.cpos -> JClause.T list
  val infer_sup : Proof.context -> (JClause.T * (JLit.lpos * JClause.cpos)) -> (JClause.T * JClause.full_pos) -> JClause.T list
  val infer_eres : Proof.context -> JClause.T -> JClause.cpos -> JClause.T list
  val infer_efact : Proof.context -> JClause.T -> ((JLit.lpos * JClause.cpos) * (JLit.lpos * JClause.cpos)) -> JClause.T list
  val infer_arg_cong : Proof.context -> JClause.T -> JClause.cpos -> JClause.T list
  val infer_bool_hoist : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_false_elim : Proof.context -> JClause.T -> (JLit.lpos * JClause.cpos) -> JClause.T list
  val simp_false_elim : Proof.context -> JClause.T -> (JLit.lpos * JClause.cpos) -> JClause.T list
  val infer_bool_rw : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_eq_hoist : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_neq_hoist : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_forall_hoist : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_exists_hoist : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_forall_rw : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_exists_rw : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val forward_simplify :
    Proof.context
    -> { forward: bool, cheap: bool }
    -> JClause.T list
    -> (int * JLit.lpos) Term_Index.T
    -> (int * JClause.full_pos) Term_Index.T
    -> Subsumption_Index.index
    -> JClause.T
    -> { simplifications: JClause.T list, archive: JClause.T list }
  val backward_simplify :
    Proof.context
    -> JClause.T list
    -> (int * JLit.lpos) Term_Index.T
    -> (int * JClause.full_pos) Term_Index.T
    -> Subsumption_Index.index
    -> JClause.T
    -> JClause.T list * JClause.T list * JClause.T list
  val infer_clauses :
    Proof.context -> JClause.T list -> JClause.T -> (int * JClause.full_pos) Term_Index.T
    -> JClause.T list
  (* *)
  structure Passive_Set : HEAP
  val init_passive_set : JClause.T list -> Passive_Set.T
  val seq_of_passive_set : Passive_Set.T -> JClause.T Seq.seq
  datatype step_result = Unsat | MaybeSat | Next 
  type prover_state =
    { context: Proof.context
    , countdown: int
    , passive: Passive_Set.T
    , active: JClause.T list
    , green_index: (int * JClause.full_pos) Term_Index.T
    , unit_index: (int * JLit.lpos) Term_Index.T
    , subsumption_index: Subsumption_Index.index
    , archive: JClause.T list
    }
  (* original exception + prover state before the exception was raised *)
  exception JEHA_EXCEPTION of exn * prover_state
  val given_clause_loop : bool -> prover_state -> step_result * prover_state
  val given_clause_step : prover_state -> step_result * prover_state
  val try_saturate : Proof.context -> thm list -> step_result * prover_state
  val make_clause_db : prover_state -> int -> JClause.T
  val select_given_clause : Passive_Set.T -> JClause.T * Passive_Set.T
  (* DEBUG *)
  val ml_bool_of : term -> bool
end

structure Jeha : JEHA =
struct

val UNIFIER_CUTOFF = 2

(* oc function from the PhD thesis
logically:
  outer_clausify b s c = clauses of (if b then s else \<not>s) \<or> c
Distribute the first logical symbol (\<and>, \<or>, \<longrightarrow>) over the clause (removing prefix
of negations above and below) *)
fun outer_clausify ctxt b (@{term Not} $ s) c = outer_clausify ctxt (not b) s c
  | outer_clausify ctxt b (Const (@{const_name HOL.disj}, _) $ s $ t) c =
    if b                     
      then [fold (JClause.add_literal ctxt) [JLit.of_term_signed b s, JLit.of_term_signed b t] c]
      else
        [ JClause.add_literal ctxt (JLit.of_term_signed b s) c
        , JClause.add_literal ctxt (JLit.of_term_signed b t) c
        ]
  | outer_clausify ctxt b (Const (@{const_name HOL.conj}, _) $ s $ t) c =
    if b
      then
        [ JClause.add_literal ctxt (JLit.of_term_signed b s) c
        , JClause.add_literal ctxt (JLit.of_term_signed b t) c
        ]
      else [fold (JClause.add_literal ctxt) [JLit.of_term_signed b s, JLit.of_term_signed b t] c]
  | outer_clausify ctxt b (Const (@{const_name HOL.implies}, _) $ s $ t) c =
      (* rewrite as disjunction, additional not will be removed in JLit.mk_pred *)
      outer_clausify ctxt b (HOLogic.mk_disj (HOLogic.mk_not s, t)) c
  (* FIXME: Making HO Sup work p.7 says: never simplify \<longleftrightarrow>. What does this mean
  concretely? (Isabelle represents \<longleftrightarrow> as HOL.eq) *)
  | outer_clausify ctxt b (Const (@{const_name HOL.eq}, _) $ s $ t) c =
      [JClause.add_literal ctxt (s, t, b) c]
  (* FIXME: add forall, exists (make fresh var, increment maxidx) *)
  | outer_clausify ctxt b s c = []

(*** Rules ***)

(** Simplification **)

(* Syntactic tautology deletion 1 (TD1) (Schulz) *)
fun contains_syntactic_equation [] = false
  | contains_syntactic_equation c =
      exists (fn (s, t, is_positive) => is_positive andalso s aconv t) c

(* Syntactic tautology deletion 2 (TD2) (Schulz) *)
fun contains_syntactic_complementaries [] = false
  | contains_syntactic_complementaries (l as (s, t, b) :: ls) =
      exists (curry JLit.aconv (s, t, not b)) ls orelse contains_syntactic_complementaries ls

(* FIXME: implement semantic tautology deletion? *)

(* Deletion of duplicated literals (DD) (Schulz) *)
fun simp_delete_duplicated_lits ctxt c =
  (* (writeln "DD"; *)
  let
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
      then NONE
      else
        (Jeha_Common.trace_msg_simp_steps ctxt (fn () => "deleted duplicated literals in " ^ JClause.pretty_clause ctxt c);
        SOME (
          c'
          |> JClause.recompute_selected ctxt 
          |> JClause.refresh_id ()
          |> JClause.set_origin
            (Jeha_Log.DeleteDuplicatedLits
              { premise = JClause.id c, duplicate_cposs = cposs_of_dups })
        ))
  end
  (* ) *)

(* Deletion of resolved literals (DR) (Schulz) *)
fun simp_delete_resolved_lits ctxt c =
  (* (writeln "DR"; *)
  let
    (* literal of the from s \<noteq> s *)
    fun is_false_disequation (s, t, is_positive) = not is_positive andalso s aconv t
    val cposs =
      c
      |> JClause.literals
      |> map_index (fn x => x)
      |> filter (is_false_disequation o snd)
      |> map fst
    val c' = JClause.delete_lits_at ctxt cposs c
  in
    if JClause.length c' = JClause.length c
      then NONE
      else
        (Jeha_Common.trace_msg_simp_steps ctxt (fn () =>
          "deleted resolved literals in " ^ JClause.pretty_clause ctxt c);
        SOME (
          c'
          |> JClause.recompute_selected ctxt
          |> JClause.refresh_id ()
          |> JClause.set_origin
            (Jeha_Log.DeleteResolvedLits { premise = JClause.id c, cposs = cposs })
        ))
  end
  (* ) *)

fun is_pos_unit { literals = [(_, _, true)], ... } = true
  | is_pos_unit _ = false

(* Rewriting of positive (RP) or negative literals (RN) simplification (Schulz) *)
(* FIXME: Implement side conditions following
  https://github.com/leanprover-community/duper/blob/aab52219c72cb52951832c8e985e1dc3e9497af9/Duper/Rules/Demodulation.lean#L51
*)
fun impl_simp_rewrite_lits positive ctxt (unit_clause, lp) (target_clause, j as (_, _, target_cp)) =
  (* (writeln (if positive then "RP" else "RN"); *)
  (* check unit_clause *)
  if not (is_pos_unit unit_clause) then NONE else
  (* check that to be rewritten literal is indeed positive / negative *)
  if not (positive = #3 (JClause.lit_at target_cp target_clause)) then NONE else
  let
    (* in particular: ensure the variables of `to` are distinct from those of target_clause *)
    val unit_shift = JClause.maxidx target_clause + 1
    val unit_clause = JClause.incr_indexes unit_shift unit_clause
    val (from, to) =
      apply2
        (JLit.term_at_lpos (the_single (JClause.literals unit_clause)))
        (lp, JLit.swap_lpos lp) (* Schulz: (s, t) *)
    val target_term = JClause.subterm_at_full_pos target_clause j (* Schulz: u *)
    val matchers =
      Jeha_Unify.matchers
        (Context.Proof ctxt)
        (JClause.maxidx_of2 (unit_clause, target_clause))
        [(from, target_term)]
    fun build_conclusion matcher =
      let
        val msg = (fn () => "   " ^ (if positive then "(RP)" else "(RN)")
          ^ " rewriting " ^ Jeha_Common.pretty_term ctxt target_term
          ^ " in " ^ JClause.pretty_clause ctxt target_clause
          ^ " with " ^ Jeha_Common.pretty_term ctxt from
          ^ " \<mapsto> " ^ Jeha_Common.pretty_term ctxt to)
        val (from, to) = apply2 (JTerm.norm_beta_eta_qeta_env matcher) (from, to)
      in
        (* NOTE: subst_term is only for Pattern.match, not Unify.matchers! *)
        (* Schulz: \<sigma>(s) > \<sigma>(t) *)
        if SOME GREATER <> Jeha_Order.kbo (from, to)
          then NONE
        else
        let
          val rewritten_clause =
            target_clause
            |> JClause.map_at_full_pos j (K to)
            |> JClause.norm_beta_eta_qeta ctxt
            |> JClause.set_maxidx (Envir.maxidx_of matcher)
          val rewriting_clause = JClause.dummy [(from, to, true)]
          val rewriting_smaller_than_rewritten = (fn () =>
            SOME LESS = JClause.kbo (rewriting_clause, rewritten_clause))
        in
          if positive andalso not (rewriting_smaller_than_rewritten ()) then NONE else
          (Jeha_Common.trace_msg_simp_steps ctxt msg;
          (* writeln ("      " ^ (Jeha_Common.pretty_tenv ctxt (Envir.term_env matcher))); *)
          (JClause.norm_beta_eta_qeta ctxt rewritten_clause)
          |> JClause.norm_negative_predicate_literals ctxt
          |> JClause.recompute_selected ctxt
          |> JClause.refresh_id ()
          |> JClause.set_origin (
              (if positive then Jeha_Log.RewritePositiveLits else Jeha_Log.RewriteNegativeLits)
                { unit = JClause.id unit_clause
                , unit_shift = unit_shift
                , unit_orientation = lp
                , right_premise = JClause.id target_clause
                , subterm = j 
                , substitution = matcher}
             )
          |> SOME)
        end
      end
  in
    matchers
    |> Seq.take UNIFIER_CUTOFF
    |> Seq.map_filter build_conclusion
    |> Seq.pull
    |> Jeha_Common.map_some #1
  end
  (* ) *)

(* Rewriting of positive literals (RP) simplification (Schulz) *)
val simp_rewrite_positive_lits = impl_simp_rewrite_lits true

(* Rewriting of positive literals (RN) simplification (Schulz) *)
val simp_rewrite_negative_lits = impl_simp_rewrite_lits false

(* active units rewrite given clause *)
fun forward_rewrite ctxt active unit_index given_clause =
  let
    val all_disabled = Config.get ctxt Jeha_Common.disable_all
    fun cfg_rule rule = if not all_disabled orelse Config.get ctxt rule then true else false
    val cfg_rp = cfg_rule Jeha_Common.rule_rewrite_positive_lits
    val cfg_rn = cfg_rule Jeha_Common.rule_rewrite_negative_lits
    val green_subterms_in_given_clause =
      JClause.green_full_poss_of given_clause
      |> map (`(JClause.subterm_at_full_pos given_clause))
    fun candidate_units t : (JClause.T * JLit.lpos) list =
      Term_Index.get_generalizations t unit_index
      (* FIXME: replace this by `map`, once we delete from the index. *)
      |> map_filter (fn (id, lp) =>
        case find_first (curry op= id o JClause.id) active of
          SOME active_clause => SOME (active_clause, lp)
        | NONE => NONE)
  in
    green_subterms_in_given_clause
    |> get_first (fn (t, fp) =>
    candidate_units t
    |> get_first (fn (c, lp) =>
    merge_options
      ( if cfg_rp then simp_rewrite_positive_lits ctxt (c, lp) (given_clause, fp) else NONE
      , if cfg_rn then simp_rewrite_negative_lits ctxt (c, lp) (given_clause, fp) else NONE
      )
    ))
  end

(* given clause (a unit) rewrites active clauses *)
fun backward_rewrite ctxt active green_index given_clause
  : { simplifications : JClause.T list, archive : JClause.T list }
=
  if not (JClause.is_unit given_clause) then { simplifications = [], archive = [] } else
  let
    val all_disabled = Config.get ctxt Jeha_Common.disable_all
    fun cfg_rule rule = if not all_disabled orelse Config.get ctxt rule then true else false
    val cfg_rp = cfg_rule Jeha_Common.rule_rewrite_positive_lits
    val cfg_rn = cfg_rule Jeha_Common.rule_rewrite_negative_lits
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
          | NONE => (case find_first (curry op= id o JClause.id) active of
              SOME active_clause => (case if cfg_rp then (simp_rewrite_positive_lits ctxt (given_clause, lp) (active_clause, fp)) else NONE of
                  SOME result => { simplifications = result::simplifications, archive = active_clause::archive }
                | NONE => (case if cfg_rn then (simp_rewrite_negative_lits ctxt (given_clause, lp) (active_clause, fp)) else NONE of
                    SOME result => { simplifications = result::simplifications, archive = active_clause::archive }
                  | NONE => acc))
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
  (* (writeln "NS"; *)
  if is_pos_unit unit_clause then NONE else
  (* check that to be deleted literal is indeed positive *)
  if not (true = #3 (JClause.lit_at target_cp target_clause)) then NONE else
  let
    val unit_shift = (JClause.maxidx target_clause + 1)
    val unit_clause = JClause.incr_indexes unit_shift unit_clause
    val maxidx = JClause.maxidx_of2 (unit_clause, target_clause)
    val unit_lit = the_single (JClause.literals unit_clause) (* Schulz: s, t *)
    val (s, t, false) = JLit.orient unit_lp unit_lit
    val target_lit = JClause.lit_at target_cp target_clause (* Schulz: u[], u[]*)
    val (u, v, true) = target_lit
    val matcher =
      [(s, u), (t, v)]
      |> Jeha_Unify.matchers (Context.Proof ctxt) maxidx
      |> Seq.pull
    (* tracing *)
    val msg = (fn () => "   " ^ "(NS)"
      ^ " deleting " ^ JClause.pretty_clause ctxt (JClause.dummy [target_lit])
      ^ " in " ^ JClause.pretty_clause ctxt target_clause
      ^ " with " ^ JClause.pretty_clause ctxt (JClause.dummy [unit_lit]))
  in
    if is_some matcher
      then let val _ = Jeha_Common.trace_msg_simp_steps ctxt msg in
        target_clause
        |> JClause.delete_lit_at ctxt target_cp
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ()
        |> JClause.set_origin (Jeha_Log.NegativeSimplifyReflect
            { literal = target_cp
            , right_premise = JClause.id target_clause
            , unit = JClause.id unit_clause
            , matcher = #1 (the matcher)
            , unit_shift = unit_shift
            , unit_orientation = unit_lp }
           )
        |> SOME 
      end
      else NONE
  end
  (* ) *)

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
      Jeha_Common.map_some (chop_end_until_green (fst term_pair)) disagreement_pos
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
    val (lhs, rhs, true) = unit_lit (* Schulz: s, t *)
    val (target_lhs, target_rhs, _) = target_lit (* Schulz: u[], u[]*)
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
          |> apply2 (Jeha_Unify.matchers (Context.Proof ctxt) maxidx)
          |> (fn (left_matchers, right_matchers) =>
            (Seq.map (pair JLit.Left) left_matchers, Seq.map (pair JLit.Right) right_matchers))
          |> Seq.interleave
          |> Seq.pull
          |> Jeha_Common.map_some fst
      in
        Jeha_Common.map_some (pair prefix_of_disagreements) matcher
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
          |> Jeha_Common.map_some (pair unit_shift)
  end

(* Positive simplify-reflect (PS) simplification (Schulz)
      s = t    u\<langle>\<sigma>(s)\<rangle>\<^sub>p \<noteq> u\<langle>\<sigma>(t)\<rangle>\<^sub>p \<or> R
      --------------------------------
      s = t              R
*)
fun simp_positive_simplify_reflect ctxt unit_clause (target_clause, target_cp) =
  (* (writeln "PS"; *)
  if not (is_pos_unit unit_clause) then NONE else
  (* check that to be deleted literal is indeed negative *)
  if not (false = #3 (JClause.lit_at target_cp target_clause)) then NONE else
  let
    val lit = the_single (JClause.literals unit_clause) (* Schulz: s, t *)
    val target_lit = JClause.lit_at target_cp target_clause (* Schulz: u[], u[]*)
    val matcher =
      literal_can_match_single_disagreement
        ctxt (JClause.maxidx unit_clause, lit) (JClause.maxidx target_clause, target_lit)
    (* tracing *)
    val msg = (fn () => "   " ^ "(PS)"
      ^ " deleting " ^ JClause.pretty_clause ctxt (JClause.dummy [target_lit])
      ^ " in " ^ JClause.pretty_clause ctxt target_clause
      ^ " with " ^ JClause.pretty_clause ctxt (unit_clause))
  in
    case matcher of
      SOME (unit_shift, (disagreement, (unit_orientation, matcher))) =>
        let val _ = Jeha_Common.trace_msg_simp_steps ctxt msg in
        target_clause
        |> JClause.delete_lit_at ctxt target_cp
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ()
        |> JClause.set_origin (
            Jeha_Log.PositiveSimplifyReflect
            { unit = JClause.id unit_clause
            , unit_shift = unit_shift
            , matcher = matcher
            , unit_orientation = unit_orientation
            , right_premise = JClause.id target_clause
            (* This fixed to be JLit.Left because there is symmetry in the orientation of the unit
            and which side of the target literal we apply the rewrite to. *)
            , disagreement = (disagreement, JLit.Left, target_cp) }
          )
        |> SOME 
        end
      | NONE => NONE
  end
  (* ) *)

(* Equality subsumption (ES) redundancy check (Schulz) *)
fun equality_subsumes ctxt (unit_clause, target_clause) =
  if not (is_pos_unit unit_clause) then false else
  let
    (* Schulz: s, t *)
    val unit_lit = (JClause.maxidx unit_clause, the_single (JClause.literals unit_clause))
    val positive_lits =
      map (pair (JClause.maxidx target_clause)) (filter #3 (JClause.literals target_clause))
    val exists_matcher =
      exists (is_some o literal_can_match_single_disagreement ctxt unit_lit) positive_lits
    val _ = if exists_matcher then Jeha_Common.trace_msg_simp_steps ctxt (fn () =>
      "equality subsumed by " ^ JClause.pretty_clause ctxt unit_clause) else ()
  in
    exists_matcher
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
    fun trace_subsumed unit subsumed =
      subsumed andalso
        (Jeha_Common.trace_msg_simp_steps ctxt (fn () => "subsumed by " ^ JClause.pretty_clause ctxt unit); true)
    val all_disabled = Config.get ctxt Jeha_Common.disable_all
    fun if_cfg rule f = if not all_disabled orelse Config.get ctxt rule then f () else false
    
    fun clause_subsumed_by active_clause_id =
      (case find_first (curry op= active_clause_id o JClause.id) active of
        SOME active_clause =>         
          if_cfg
            Jeha_Common.rule_clause_subsumption
            (fn _ => Jeha_Subsumption.subsumes (Context.Proof ctxt) (active_clause, clause)
              |> trace_subsumed active_clause)
      | NONE => false)

    fun is_subsumed_folder active_id already_subsumed =
      already_subsumed orelse clause_subsumed_by active_id

    val subsumed =
      Subsumption_Index.fold_subsuming clause is_subsumed_folder subsumption_index false
  in
    subsumed
  end

fun get_backward_subsumed ctxt given_clause active subsumption_index : int list =
  let
    fun trace_subsumed unit subsumed =
      subsumed andalso
        (Jeha_Common.trace_msg_simp_steps ctxt (fn () => "subsumed by " ^ JClause.pretty_clause ctxt unit); true)
    val all_disabled = Config.get ctxt Jeha_Common.disable_all
    fun if_cfg rule f = if not all_disabled orelse Config.get ctxt rule then f () else false

    fun is_subsumed_by_given_clause active_clause_id =
      (case find_first (curry op= active_clause_id o JClause.id) active of
        SOME active_clause =>         
          if_cfg
            Jeha_Common.rule_clause_subsumption
            (fn _ => Jeha_Subsumption.subsumes (Context.Proof ctxt) (given_clause, active_clause)
              |> trace_subsumed active_clause)
      | NONE => false)
      
    val subsumed_candidates =
      Subsumption_Index.fold_subsumed given_clause (curry op::) subsumption_index []
    
    val subsumed_actives = filter is_subsumed_by_given_clause subsumed_candidates
  in
    subsumed_actives
  end

(* FIXME: implement forwards and backwards variants using indexing *)
fun is_equality_subsumed ctxt active c =
  let
    val all_disabled = Config.get ctxt Jeha_Common.disable_all
    (* val _ = if all_disabled then writeln "REDUNDANCY CHECKS DISABLED" else () *)
    fun if_cfg rule f = if not all_disabled orelse Config.get ctxt rule then f () else false
    fun equality_subsumed_by active_clause =
      if_cfg
        Jeha_Common.rule_equality_subsumption
        (fn _ => equality_subsumes ctxt (active_clause, c))
  in
    exists
      (fn active_clause => equality_subsumed_by active_clause)
      active
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
fun simp_bool_outer_claus ctxt (c, i) =
  let val lit = JClause.lit_at i c in
  if not (JLit.is_pred lit) then [] else
  let
    val (s, b) = lit |> JLit.dest_pred ||> ml_bool_of
    val c' = JClause.delete_lit_at ctxt i c
    (* Meaning: "if b then PosOuterClaus else NegOuterClaus" *)
    val clausified = outer_clausify ctxt b s c'
  in
    if null clausified then [] else (* in particular if head of s is not a logical symbol *)
    clausified
    |> map_index
      (fn (index, clause) =>
        clause
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.set_origin (
          Jeha_Log.SimpPosNegOuterClaus
            { premise = JClause.id c, literal = i, conclusion_index = index }
        )
      )
    (* FIXME: map might be sufficient, i.e. no need for a fold *)
    |> (fn clauses =>
        fold
          (fn clause => fn (unit_value, acc) =>
            (unit_value, JClause.refresh_id unit_value clause :: acc))
          clauses
          ((), [])
       )
    |> #2
  end
  end

(* EqOuterClaus and NeqOuterClaus inferences *)
fun infer_eq_neq_outer_claus ctxt c i =
  let
    val (s, t, b) = JClause.lit_at i c
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
      val unifiers = Jeha_Unify.smash_unifiers (Context.Proof ctxt) [(t, u)] env
    in
      error "impl_infer_sup unimplemented"
    end
  end
*)


(* Sup inference *)
fun infer_sup ctxt (d, (lp, cp)) (c, u_pos) =
  let
    val () = Jeha_Common.trace_msg_sup ctxt (K ("Sup start: "
      ^ JClause.pretty_clause ctxt d ^ " " ^ JClause.pretty_clause ctxt c))
    val left_premise_shift = JClause.maxidx c + 1
    val d = JClause.incr_indexes left_premise_shift d
    val env = Envir.empty (JClause.maxidx_of2 (c, d))
    val rewriting_literal = JClause.lit_at cp d (* t \<approx> t' *)
    val (t, t', is_pos_eq) = JLit.orient lp rewriting_literal
    val u = JClause.subterm_at_full_pos c u_pos
  in
    if not is_pos_eq then
      (Jeha_Common.trace_msg_sup ctxt (K "Sup fail: not positive");
        []) else
    if JTerm.might_be_fluid u then
      (Jeha_Common.trace_msg_sup ctxt (K "Sup fail: might be fluid");
        []) else (* 1. *)
    if is_Var u andalso JClause.occurs_deeply u c then
      (Jeha_Common.trace_msg_sup ctxt (K "Sup fail: deeply occuring var");
        []) else (* 2. *)
    (* FIXME: 3. variable condition ... *)
    let
      val _ = Jeha_Common.trace_msg_sup ctxt (fn () =>
        "Sup: " ^ JClause.pretty_clause ctxt d ^ " into " ^ JClause.pretty_clause ctxt c)
      val unifiers = Jeha_Unify.smash_unifiers (Context.Proof ctxt) [(t, u)] env
      val _ = Jeha_Common.trace_msg_sup ctxt (fn () =>
        "Sup: " ^ Jeha_Common.pretty_term ctxt t ^ " ?= " ^ Jeha_Common.pretty_term ctxt u)
      val (unifiers, _) = Seq.chop UNIFIER_CUTOFF unifiers
      fun build_conclusion unifier =
        let
          val (c, d) =
            (c, d)
            |> apply2 (JClause.norm_beta_eta_qeta_env ctxt unifier)
            |> apply2 (JClause.recompute_selected ctxt)
          val u_eligible = JClause.is_eligible_full_pos c u_pos
          (* This checks for strict eligibility of cp because the literal at cp is positive. *)
          val tt'_eligible = JClause.is_eligible_cpos d cp
          (* FIXME: according to the thesis this is skipped for performance
          reasons, would explain the difficulty in understanding zipperpositions
          implementation *)
          val c_comp_d = JClause.kbo (c, d)
          (* val _ = writeln ("c_comp_d " ^ @{make_string} c_comp_d) *)
          val d' = JClause.delete_lit_at ctxt cp d
          (* this relies on normalization not destroying green / top level positions, i.e.
          (t = t')\<sigma> = (t\<sigma> = t'\<sigma>) and C<u>\<sigma> = C\<sigma><u\<sigma>> *)
          val (t, t', _) = JLit.orient lp (JClause.lit_at cp d)
          val ct' = JClause.map_at_full_pos u_pos (K t') c (* FIXME: recompute selected *)
          val t_comp_t' = Jeha_Order.kbo (t, t')
          (* val _ = writeln ("t_comp_t' " ^ @{make_string} t_comp_t') *)
        in
          (* order restrictions *)
          if SOME LESS = t_comp_t' orelse SOME EQUAL = t_comp_t' then
            (Jeha_Common.trace_msg_sup ctxt (K "Sup fail: t\<sigma> \<preceq> u\<sigma> ");
              NONE) else (* 5. *)
          if not u_eligible then
            (Jeha_Common.trace_msg_sup ctxt (K "Sup fail: u not eligible");
              NONE) else (* 6. *)
          if SOME LESS = c_comp_d orelse SOME EQUAL = c_comp_d then
            (Jeha_Common.trace_msg_sup ctxt (K "Sup fail: C\<sigma> \<preceq> D\<sigma>");
              NONE) else (* 7. *)
          if not tt'_eligible then
            (Jeha_Common.trace_msg_sup ctxt (K "Sup fail: t \<approx> t' not eligible");
              NONE) else (* 8. *)
          (* FXIME 9. 10. *)
          JClause.combine ctxt d' ct'
          |> JClause.norm_negative_predicate_literals ctxt
          |> JClause.recompute_selected ctxt
          |> JClause.refresh_id ()
          |> JClause.set_origin
              (Jeha_Log.Sup
                { left_premise = JClause.id d
                , left_premise_shift = left_premise_shift
                , right_premise = JClause.id c
                , literal = (lp, cp)
                , subterm = u_pos
                , substitution = unifier })
          |> tap (fn concl =>
            (Jeha_Common.trace_msg_sup ctxt (K ("Sup concl: " ^ JClause.pretty_clause ctxt concl))))
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
  (active : JClause.T list)
  (green_index: (int * JClause.full_pos) Term_Index.T)
  : JClause.T list
=
  let
    (* the equality literals that are being eliminated *)
    val ts_in_given_clause : (term * (JLit.lpos * JClause.cpos)) list =
      (Jeha_Common.cartesian_product [JLit.Left, JLit.Right] (JClause.cposs_of given_clause))
      |> map (`(fn (lp, cp) => JClause.subterm_at_full_pos given_clause ([], lp, cp)))
    fun candidate_green_subterms t : (JClause.T * JClause.full_pos) list =
      Term_Index.get_unifiables t green_index
      (* FIXME: replace this by `map`, once we delete from the index. *)
      |> map_filter (fn (id, fp) =>
        case find_first (curry op= id o JClause.id) active of
          SOME active_clause => SOME (active_clause, fp)
        | NONE => NONE)
  in
    ts_in_given_clause
    |> maps (fn (t, (lp, cp)) =>
        candidate_green_subterms t
        |> maps (fn (c, u_pos) =>
            infer_sup ctxt (given_clause, (lp, cp)) (c, u_pos)))
  end

(* ERes inference *)
fun infer_eres (ctxt : Proof.context) c cp =
  let
    val (u, u', is_pos_eq) = JClause.lit_at cp c
    val unifiers =
      Jeha_Unify.smash_unifiers (Context.Proof ctxt) [(u, u')] (Envir.empty (JClause.maxidx c))
    val (unifiers, _) = Seq.chop UNIFIER_CUTOFF unifiers
    fun build_conclusion unifier =
      let
        val c = c |> JClause.norm_beta_eta_qeta_env ctxt unifier |> JClause.recompute_selected ctxt
      in
        if not (JClause.is_eligible_cpos c cp) then NONE else
        c
        |> JClause.delete_lit_at ctxt cp
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ()
        |> JClause.set_origin
          (Jeha_Log.ERes { premise = JClause.id c, literal = cp, substitution = unifier })
        |> SOME
      end
  in
    if is_pos_eq
      then []
      else map_filter build_conclusion unifiers
  end

(* EFact inference *)
fun infer_efact ctxt c ((lp', cp'), (lp, cp)) =
  let
    val () = Jeha_Common.trace_msg_e_fact ctxt (fn () =>
      "EFact start " ^ JClause.pretty_clause ctxt c)
    val (u', v', is_pos') = JLit.orient lp' (JClause.lit_at cp' c)
    val (u, v, is_pos) = JLit.orient lp (JClause.lit_at cp c)
    val () = Jeha_Common.trace_msg_e_fact ctxt (fn () =>
      "EFact: " ^ Jeha_Common.pretty_term ctxt u ^ " ?= " ^ Jeha_Common.pretty_term ctxt u')
    val unifiers =
      Jeha_Unify.smash_unifiers (Context.Proof ctxt) [(u, u')] (Envir.empty (JClause.maxidx c))
    val (unifiers, _) = Seq.chop UNIFIER_CUTOFF unifiers
    val nothing_selected_in_c = JClause.selected c = []
    fun build_conclusion unifier =
      let
        val () = Jeha_Common.trace_msg_e_fact ctxt (fn () => "EFact build_conclusion")
        val c = c |> JClause.norm_beta_eta_qeta_env ctxt unifier
        val (u', v', _) = JLit.orient lp' (JClause.lit_at cp' c)
        val uv_literal = JClause.lit_at cp c
        val (u, v, _) = JLit.orient lp uv_literal
        val u_v_comp = Jeha_Order.kbo (u, v)
        val uv_maximal = Jeha_Order.is_maximal JLit.kbo false uv_literal (JClause.literals c)
      in
        if SOME EQUAL = u_v_comp orelse SOME LESS = u_v_comp then
          (Jeha_Common.trace_msg_e_fact ctxt (K "EFact fail: u\<sigma> \<preceq> v\<sigma>");
            NONE) else
        if not uv_maximal then
          (Jeha_Common.trace_msg_e_fact ctxt (K "EFact fail: (u=v) not maximal");
            NONE) else
        if not nothing_selected_in_c then
          (Jeha_Common.trace_msg_e_fact ctxt (K "EFact fail: something selected");
            NONE) else
        c
        |> JClause.delete_lit_at ctxt (Int.max (cp, cp'))
        |> JClause.delete_lit_at ctxt (Int.min (cp, cp'))
        |> JClause.add_literal ctxt (v, v', false)
        |> JClause.add_literal ctxt (u, v', true)
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ()
        |> JClause.set_origin
            (Jeha_Log.EFact
              { premise = JClause.id c
              , left_literal = (lp', cp')
              , right_literal = (lp, cp)
              , substitution = unifier })
        |> tap (fn concl => Jeha_Common.trace_msg_e_fact ctxt (K ("EFact concl: " ^ JClause.pretty_clause ctxt concl)))
        |> SOME
      end
    in
      if not (is_pos andalso is_pos') then
        (Jeha_Common.trace_msg_e_fact ctxt (K "EFact fail: negative literal");
          []) else
      if cp' = cp then
        (Jeha_Common.trace_msg_e_fact ctxt (K "EFact fail: equal positions");
          []) else
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

(* number of extra conclusions generated by ArgCong if the return type of s is a
type variable *)
val ARG_CONG_EXTRA_CONCLUSIONS = 2

fun infer_arg_cong ctxt c cpos =
  let val (s, s', b) = JClause.lit_at cpos c in
  if not b then [] else
  let
    val s_num_of_args = length (Term.binder_types (fastype_of s))

    fun mk_fresh_typ idx = TVar (("'a", idx), Sign.defaultS (Proof_Context.theory_of ctxt))
    fun mk_fresh_var idx = Var (("x_ac", idx), mk_fresh_typ idx)

    val maxidx = JClause.maxidx c

    val new_maxidx = s_num_of_args + ARG_CONG_EXTRA_CONCLUSIONS + 1

    val fresh_result_type = mk_fresh_typ new_maxidx
    val xs_idxs = (maxidx + 1) upto (new_maxidx - 1)
    val fresh_variables = map mk_fresh_var xs_idxs

    fun build_conclusion fresh_variables =
      let
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

        val new_clause =
          c
          |> JClause.map_at_cpos cpos (K new_literal) (* FIXME: recompute selected *)
          |> JClause.norm_beta_eta_qeta_env ctxt unifier
          |> JClause.recompute_selected ctxt
          |> JClause.set_maxidx new_maxidx
          |> JClause.refresh_id ()
          |> JClause.set_origin
              (Jeha_Log.ArgCong 
                { premise = JClause.id c
                , substitution = unifier
                , literal = cpos
                , vars = map (JTerm.norm_beta_eta_qeta_env unifier) fresh_variables })
      in
        if not (JClause.is_eligible_cpos new_clause cpos) then NONE else
        SOME new_clause
      end
  in
    prefixes1 fresh_variables
    |> map_filter (fn vars => build_conclusion vars handle Pattern.Unif => NONE)
  end
  end

fun infer_bool_hoist ctxt c (u_pos as (_, _, cpos)) =
  let
    val u = JClause.subterm_at_full_pos c u_pos
    val u_in_positive_lit = JLit.is_positive (JClause.lit_at cpos c)
    val u_eligible = JClause.is_eligible_full_pos c u_pos
    val u_typ = fastype_of u
    (* raises TUNIFY (from Sign.typ_unify) *)
    fun build_conclusion _ =
      let
        val (unifier, maxidx) =
          Sign.typ_unify
            (Proof_Context.theory_of ctxt)
            (u_typ, @{typ "HOL.bool"})
            (Vartab.empty, JClause.maxidx c)
        val u_eq_true = JLit.mk_pred u true
        val unifier = Envir.Envir { maxidx = maxidx, tenv = Vartab.empty, tyenv = unifier }
      in
        if
          JTerm.is_variable_headed u (* 2. *)
          orelse JClause.is_position_of_fully_applied_logical_symbol u_pos c (* 2. *)
          orelse not u_eligible (* 3. *)
          orelse (u_in_positive_lit andalso [] = #1 u_pos) (* 4. *)
        then
          []
        else
          c
          |> JClause.map_at_full_pos u_pos (K @{term "HOL.False"}) (* FIXME: recompute selected *)
          |> JClause.add_literal ctxt u_eq_true
          |> JClause.norm_beta_eta_qeta_env ctxt unifier
          |> JClause.norm_negative_predicate_literals ctxt
          |> JClause.recompute_selected ctxt
          |> JClause.refresh_id ()
          |> JClause.set_origin
            (Jeha_Log.BoolHoist { premise = JClause.id c, subterm = u_pos, substitution = unifier })
          |> single
        end
  in
    (build_conclusion () handle Type.TUNIFY => [])
  end

(* FIXME: apply as simplification if unifier is the identity *)
fun impl_simp_infer_false_elim as_simplification ctxt c (lp, cp) =
  let
    (* val _ = writeln ("in False_elim with" ^ @{make_string} (lp, cp)) *)
    val (s, s', b) = JClause.lit_at cp c |> JLit.orient lp
    val unifiers =
      if not b
        then Seq.empty
      else if as_simplification
        then if s aconv @{term "False"} andalso s' aconv @{term "True"}
          then Seq.single (Envir.empty (JClause.maxidx c))
          else Seq.empty
      else
        Jeha_Unify.smash_unifiers
          (Context.Proof ctxt)
          [(s, @{term "False"}), (s', @{term "True"})]
          (Envir.empty (JClause.maxidx c))
    val (unifiers, _) = Seq.chop UNIFIER_CUTOFF unifiers
    fun build_conclusion unifier =
      let
        val c = c |> JClause.norm_beta_eta_qeta_env ctxt unifier |> JClause.recompute_selected ctxt
        val origin =
          if as_simplification
            then
              Jeha_Log.SimpFalseElim
                { premise = JClause.id c, literal = (lp, cp), substitution = unifier }
            else
              Jeha_Log.FalseElim
                { premise = JClause.id c, literal = (lp, cp), substitution = unifier }
      in
        if not as_simplification andalso not (JClause.is_eligible_cpos c cp) then NONE else (* 2. *)
        c
        |> JClause.delete_lit_at ctxt cp
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ()
        |> JClause.set_origin origin
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
    val truth_value_pairs = Jeha_Common.cartesian_product truth_values truth_values
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
  (c : JClause.T)
  (u_pos : JClause.full_pos)
  (pattern : term)
  (u_var_allowed : bool) (* this is false for BoolRw but true for the others *)
  (insert_for_u : term) (* will be \<top> or \<bottom> *)
  (disjunct_with : JLit.T option) (* this is needed for the Hoist rules *)
  : (Envir.env * JClause.T) list
=
  let val u = JClause.subterm_at_full_pos c u_pos in
  if (not u_var_allowed) andalso (is_Var u) then [] else (* BoolRw: 2. *)
  let
    val maxidx =
      Int.max
        ( Int.max (JClause.maxidx c, maxidx_of_term pattern)
        , the_default ~1 (Jeha_Common.map_some JLit.maxidx_of disjunct_with) )
    val u_at_toplevel_and_eq_to_bool_or_eq_to_var_headed_term =
      case u_pos of
        ([], lpos, cpos) =>
          let
            val (_, other_side, is_positive) = c |> JClause.lit_at cpos |> JLit.orient lpos
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
      Jeha_Unify.smash_unifiers
        (Context.Proof ctxt)
        [(u, pattern)]
        (Envir.empty (maxidx + 1))
    val (unifiers, _) = Seq.chop UNIFIER_CUTOFF unifiers
    fun build_conclusion unifier =
      let
        val c =
          c
          |> JClause.norm_beta_eta_qeta_env ctxt unifier
          |> JClause.recompute_selected ctxt
        val new_literal =
          Jeha_Common.map_some
            (JLit.norm_beta_eta_qeta_env unifier)
            disjunct_with
        val insert_for_u = JTerm.norm_beta_eta_qeta_env unifier insert_for_u

        (* FIXME: remove after debugging *)
        val u_subbed = JClause.subterm_at_full_pos c u_pos
        val _ = if type_of u_subbed <> type_of insert_for_u then
            (writeln ("TYPES DONT MATCH: " ^ Jeha_Common.pretty_term ctxt u_subbed ^ " <> " ^ Jeha_Common.pretty_term ctxt insert_for_u);
            writeln ("NORMED CLAUSE: " ^ JClause.pretty_clause ctxt c);
            writeln ("PATTERN: " ^ Jeha_Common.pretty_term ctxt pattern);
            writeln ("U: " ^ Jeha_Common.pretty_term ctxt u);
            writeln ("UNIFIER: " ^ Jeha_Common.pretty_tenv ctxt (Envir.term_env unifier));
            writeln ("INSERT FOR U:" ^ Jeha_Common.pretty_term ctxt insert_for_u);
            error "TYPESDONTMATCH")
          else ()

        val maxidx =
          Int.max
            ( Int.max (JClause.maxidx c, maxidx_of_term insert_for_u)
            , the_default ~1 (Jeha_Common.map_some JLit.maxidx_of new_literal) )
      in
        (* 3. the position of u is eligible in C w.r.t. \<sigma> *)
        if not (JClause.is_eligible_full_pos c u_pos) then NONE else
        (* 4. if the head of u is a variable ... *)
        if not u_variable_headed_condition then NONE else

        c
        |> JClause.map_at_full_pos u_pos (K insert_for_u) (* FIXME: recompute selected *)
        |> JClause.set_maxidx maxidx
        (* add the new literal if it exists, otherwise apply identity function *)
        |> the_default I (Jeha_Common.map_some (JClause.add_literal ctxt) new_literal)
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ()
        |> pair unifier
        |> SOME
      end
  in
    map_filter build_conclusion unifiers
  end
  end

fun impl_simp_bool_rw
  ctxt
  (c : JClause.T)
  (u_pos : JClause.full_pos)
  (pattern : term)
  (u_var_allowed : bool) (* this is false for BoolRw but true for the others *)
  (insert_for_u : term) (* will be \<top> or \<bottom> *)
  (disjunct_with : JLit.T option) (* this is needed for the Hoist rules *)
  : (Envir.env * JClause.T) list
=
  let val u = JClause.subterm_at_full_pos c u_pos in
  if (not u_var_allowed) andalso (is_Var u) then [] else (* BoolRw: 2. *)
  let
    val maxidx =
      Int.max
        ( Int.max (JClause.maxidx c, maxidx_of_term pattern)
        , the_default ~1 (Jeha_Common.map_some JLit.maxidx_of disjunct_with) )
    val u_at_toplevel_and_eq_to_bool_or_eq_to_var_headed_term =
      case u_pos of
        ([], lpos, cpos) =>
          let
            val (_, other_side, is_positive) = c |> JClause.lit_at cpos |> JLit.orient lpos
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
    val unifiers = if u aconv pattern then Seq.single (Envir.empty (maxidx + 1)) else Seq.empty
    val (unifiers, _) = Seq.chop UNIFIER_CUTOFF unifiers
    fun build_conclusion unifier =
      let
        val c =
          c
          |> JClause.norm_beta_eta_qeta_env ctxt unifier
          |> JClause.recompute_selected ctxt
        val new_literal =
          Jeha_Common.map_some
            (JLit.norm_beta_eta_qeta_env unifier)
            disjunct_with
        val insert_for_u = JTerm.norm_beta_eta_qeta_env unifier insert_for_u

        (* FIXME: remove after debugging *)
        val u_subbed = JClause.subterm_at_full_pos c u_pos
        val _ = if type_of u_subbed <> type_of insert_for_u then
            (writeln ("TYPES DONT MATCH: " ^ Jeha_Common.pretty_term ctxt u_subbed ^ " <> " ^ Jeha_Common.pretty_term ctxt insert_for_u);
            writeln ("NORMED CLAUSE: " ^ JClause.pretty_clause ctxt c);
            writeln ("PATTERN: " ^ Jeha_Common.pretty_term ctxt pattern);
            writeln ("U: " ^ Jeha_Common.pretty_term ctxt u);
            writeln ("UNIFIER: " ^ Jeha_Common.pretty_tenv ctxt (Envir.term_env unifier));
            writeln ("INSERT FOR U:" ^ Jeha_Common.pretty_term ctxt insert_for_u);
            error "TYPESDONTMATCH")
          else ()

        val maxidx =
          Int.max
            ( Int.max (JClause.maxidx c, maxidx_of_term insert_for_u)
            , the_default ~1 (Jeha_Common.map_some JLit.maxidx_of new_literal) )
      in
        (* FIXME: Is this condition needed? It looks like neither zip nor duper implement it
          https://github.com/leanprover-community/duper/blob/aab52219c72cb52951832c8e985e1dc3e9497af9/Duper/Rules/BoolSimp.lean#L1260
          https://github.com/sneeuwballen/zipperposition/blob/050072e01d8539f9126993482b595e09f921f66a/src/prover_calculi/booleans.ml#L1344
        (* 3. the position of u is eligible in C w.r.t. \<sigma> *)
        if not (JClause.is_eligible_full_pos c u_pos) then NONE else *)

        (* 4. if the head of u is a variable ... *)
        if not u_variable_headed_condition then NONE else

        c
        |> JClause.map_at_full_pos u_pos (K insert_for_u)
        |> JClause.set_maxidx maxidx
        (* add the new literal if it exists, otherwise apply identity function *)
        |> the_default I (Jeha_Common.map_some (JClause.add_literal ctxt) new_literal)
        |> JClause.norm_negative_predicate_literals ctxt
        |> JClause.recompute_selected ctxt
        |> JClause.refresh_id ()
        |> pair unifier
        |> SOME
      end
  in
    map_filter build_conclusion unifiers
  end
  end

fun simp_bool_rw ctxt c u_pos =
  let
    val maxidx = JClause.maxidx c
    val rw_rules =
      (* [ (fresh_variable_eq_itself, @{term "True"})
      , (HOLogic.mk_not fresh_variable_eq_itself, @{term "False"}) ]
      @ *)
      bool_rw_non_var_rules true
    fun apply_rw_rule (t, t') =
      impl_simp_bool_rw ctxt c u_pos t false t' NONE
      |> map (fn (unifier, clause) =>
        clause
        |> JClause.set_origin
          (Jeha_Log.SimpBoolRw
            { premise = JClause.id c, subterm = u_pos, subrule = (t, t'), substitution = unifier }))
  in
    maps apply_rw_rule rw_rules
  end

(* FIXME: Idea: have the rw rules as active clauses, then this is basically superposition *)
fun infer_bool_rw ctxt c u_pos =
  let
    val maxidx = JClause.maxidx c
    val fresh_typ = TVar (("'a", maxidx + 1), Sign.defaultS (Proof_Context.theory_of ctxt)) (* type of y FIXME: better name? *)
    val fresh_variable = Var (("y_brw", maxidx + 1), fresh_typ) (* y *)
    val fresh_variable_eq_itself = HOLogic.mk_eq (fresh_variable, fresh_variable)
    val rw_rules =
      [ (fresh_variable_eq_itself, @{term "True"})
      , (HOLogic.mk_not fresh_variable_eq_itself, @{term "False"}) ]
      @
      bool_rw_non_var_rules false
    fun apply_rw_rule (t, t') =
      impl_infer_bool_rw_eq_neq_fa_ex_hoist ctxt c u_pos t false t' NONE
      |> map (fn (unifier, clause) =>
        clause
        |> JClause.set_origin
          (Jeha_Log.BoolRw
            { premise = JClause.id c, subterm = u_pos, subrule = (t, t'), substitution = unifier }))
  in
    maps apply_rw_rule rw_rules
  end

datatype HoistType = Eq | Neq | Forall | Exists

fun impl_eq_neq_hoist positive ctxt c u_pos =
  let
    val maxidx = JClause.maxidx c
    val fresh_typ = TVar (("'a", maxidx + 1), Sign.defaultS (Proof_Context.theory_of ctxt)) (* type of y FIXME: better name? *)
    val fresh_x = Var (("x", maxidx + 1), fresh_typ) (* x *)
    val fresh_y = Var (("y_eqneqhoist", maxidx + 1), fresh_typ) (* y *)
    val x_eq_y_lit = (fresh_x, fresh_y, true)
    val pattern =
      (fresh_x, fresh_y)
      |> HOLogic.mk_eq
      |> not positive ? HOLogic.mk_not
    val insert_for_u = hol_bool_of (not positive)
  in
    impl_infer_bool_rw_eq_neq_fa_ex_hoist ctxt c u_pos pattern true insert_for_u (SOME x_eq_y_lit)
    |> map (fn (unifier, clause) => clause |> JClause.set_origin (
        (if positive then Jeha_Log.EqHoist else Jeha_Log.NeqHoist)
          { premise = JClause.id c, subterm = u_pos, substitution = unifier }))
  end

val infer_eq_hoist = impl_eq_neq_hoist true

val infer_neq_hoist = impl_eq_neq_hoist false

fun impl_forall_exists_hoist is_forall ctxt c u_pos =
  let
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
    val new_lit = (fresh_predicate $ fresh_x, hol_bool_of is_forall, true)
    (* \<top> / \<bottom> *)
    val insert_for_u = hol_bool_of (not is_forall)
  in
    impl_infer_bool_rw_eq_neq_fa_ex_hoist ctxt c u_pos pattern true insert_for_u (SOME new_lit)
    |> map (fn (unifier, clause) => clause |> JClause.set_origin (
        (if is_forall then Jeha_Log.ForallHoist else Jeha_Log.ExistsHoist)
          { premise = JClause.id c, subterm = u_pos, substitution = unifier, fresh_x = fresh_x }))
  end

val infer_forall_hoist = impl_forall_exists_hoist true

val infer_exists_hoist = impl_forall_exists_hoist false

(* We diverge from the o\<lambda>Sup paper to avoid skolemization. (FIXME: Experimental)
Idea: Replace \<forall>x. y x by y (SOME z. \<not> (y z))
If the universal statement holds then there is no z s.t. \<not> (y z) and the r.h.s
is also true. If the universal statement does not hold, then there is such a z
and the r.h.s. becomes false, because z witnesses \<not> (y z).
Similarly replace \<exists>x. y x by y (SOME z. y z) *)
fun impl_infer_forall_exists_rw is_forall ctxt clause u_pos =
  (* condition 5. *)
  (case u_pos of
    ([], lpos, cpos) =>
      let
        val (_, other_side, is_positive) = clause |> JClause.lit_at cpos |> JLit.orient lpos
      in
        if not is_positive then I else
        if (is_forall andalso other_side = @{term True})
          orelse (not is_forall andalso other_side = @{term False})
        then
          K []
        else
          I
      end
  | _ => I)
  (let

    val maxidx = JClause.maxidx clause
    val fresh_typ = TVar (("'b", maxidx + 1), Sign.defaultS (Proof_Context.theory_of ctxt)) (* \<beta> *)
    val fresh_predicate = Var (("y_faexrw", maxidx + 1), fresh_typ --> @{typ bool})
    
    val choice_body = (is_forall ? HOLogic.mk_not) (fresh_predicate $ Free ("z", fresh_typ))
    val skolem_symbol = HOLogic.choice_const fresh_typ $ (absfree ("z", fresh_typ) choice_body)
    val insert_for_u = fresh_predicate $ skolem_symbol

    val quantifier =
      (if is_forall then HOLogic.all_const else HOLogic.exists_const) fresh_typ
    (* \<forall> y / \<exists> y*)
    val pattern = quantifier $ fresh_predicate

    (* val _ = writeln ("FaExRw past more with u_pos" ^ @{make_string} u_pos ) *)
  in
      impl_infer_bool_rw_eq_neq_fa_ex_hoist ctxt clause u_pos pattern false insert_for_u NONE
      |> map (fn (unifier, c) => c |> JClause.set_origin (
          (if is_forall then Jeha_Log.ForallRw else Jeha_Log.ExistsRw)
            { premise = JClause.id clause, subterm = u_pos, substitution = unifier }))
  end)

val infer_forall_rw = impl_infer_forall_exists_rw true

val infer_exists_rw = impl_infer_forall_exists_rw false


(** Saturation Loop **)

(* Passive_Set *)

fun size_of_clause c =
  fold (fn (l, r, _) => fn acc => acc + size_of_term l + size_of_term r) (JClause.literals c) 0

structure Passive_Set = Heap(type elem = int * JClause.T val ord = int_ord o apply2 fst)

fun seq_of_passive_set passive =
  if Passive_Set.is_empty passive
    then Seq.empty
    else Passive_Set.min_elem passive |>> snd ||> seq_of_passive_set |> uncurry Seq.cons

(* initial clauses all have weight 0 so they are added to active set first *)
fun init_passive_set clauses = fold Passive_Set.insert (map (pair 0) clauses) Passive_Set.empty

fun add_new_clause clause = Passive_Set.insert (size_of_clause clause, clause)

fun add_new_clauses passive clauses = fold add_new_clause clauses passive

fun select_given_clause cs = Passive_Set.min_elem cs |>> snd

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
    (* tracing *)
    val ctxt = ctxt |> Config.map Jeha_Common.trace (fn s =>
      s andalso (not cheap orelse Config.get ctxt Jeha_Common.trace_cheap_simp))

    val active_units = Seq.filter (fn c => JClause.length c = 1) (Seq.of_list active)
    val all_orientations : JClause.T Seq.seq -> (JClause.T * JLit.lpos) Seq.seq =
      fn cs => Jeha_Common.seq_cartesian_product cs (Seq.of_list [JLit.Left, JLit.Right])

    (* rule configuration *)
    val all_disabled = Config.get ctxt Jeha_Common.disable_all
    (* val _ = if all_disabled then writeln "ALL SIMPLIFICATIONS DISABLED!!!" else () *)
    fun if_cfg rule = if not all_disabled orelse Config.get ctxt rule then I else K Seq.empty

    fun simp_fun_of_seq clause_seq c =
      case Seq.pull (clause_seq c) of
        NONE => []
      | SOME (c, _) => [c]

    (* FIXME: remove active_units hack *)
    val simp_funs =
      let
        val simp_bool_rewrites: JClause.T -> JClause.T Seq.seq = fn c =>
          if_cfg Jeha_Common.rule_simp_bool_rw (
            let
              val green_targets: (JClause.T * JClause.full_pos) Seq.seq =
                Seq.map (pair c) (Seq.of_list (JClause.green_full_poss_of c))
            in
              green_targets
              (* FIXME: try taking just one instead of dealing with multiple simplifiations *)
              |> Seq.maps (fn (c, u_pos) => simp_bool_rw ctxt c u_pos |> Seq.of_list)
            end);
        val simp_false_elim_rewrites: JClause.T -> JClause.T Seq.seq = fn c =>
          if_cfg Jeha_Common.rule_simp_false_elim (
            let
              val lpos_cpos_pairs =
                Jeha_Common.cartesian_product [JLit.Left, JLit.Right] (JClause.cposs_of c) 
            in
              Seq.of_list (maps (simp_false_elim ctxt c) lpos_cpos_pairs)
            end)

        (* FIXME rewrites is a misnomer inherited from rn_rp_rewrites *)
        val oc_rewrites : Jeha_Simplify.simp_fun = fn c =>
          if_cfg Jeha_Common.rule_simp_outer_claus (
          (Seq.map (pair c) (Seq.of_list (0 upto (length (JClause.literals c) - 1))))
          |> Seq.map (simp_bool_outer_claus ctxt)
          |> Seq.map_filter (fn cs => case cs of [] => NONE | _ => SOME cs)
          )
          |> Seq.pull
          |> Jeha_Common.map_some fst
          |> the_default []
        (* successful rewrites of c (NONE filtered out) *)
        val rn_rp_rewrites : JClause.T -> JClause.T list =
          the_list o forward_rewrite ctxt active unit_index
        val ps_rewrites : JClause.T -> JClause.T Seq.seq = fn c =>
          if_cfg Jeha_Common.rule_positive_simplify_reflect (
            Jeha_Common.seq_cartesian_product active_units
              (Seq.map (pair c) (Seq.of_list (0 upto (length (JClause.literals c) - 1))))
            |> Seq.map_filter (fn (unit, target) => simp_positive_simplify_reflect ctxt unit target)
          )
        val ns_rewrites : JClause.T -> JClause.T Seq.seq = fn c =>
          if_cfg Jeha_Common.rule_negative_simplify_reflect (
            Jeha_Common.seq_cartesian_product
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
                Jeha_Common.rule_delete_duplicated_lits
                (Seq.single (simp_delete_duplicated_lits ctxt)))
              (if_cfg
                Jeha_Common.rule_delete_resolved_lits
                (Seq.single (simp_delete_resolved_lits ctxt))))
      in
        (* following Schulz: RN, RP, PS, NS, DD, DR *)
        [simp_fun_of_seq simp_bool_rewrites]
        @ [simp_fun_of_seq simp_false_elim_rewrites]
        @ [oc_rewrites]
        @ (if forward then [rn_rp_rewrites] else [])
        @ map simp_fun_of_seq
          ( (if not cheap then [ps_rewrites] else [])
          @ (if not cheap then [ns_rewrites] else [])
          @ [dd_dr_rewrites] )
      end
    (* rewrite until not possible anymore *)
    val (simplifications, archive) =
      Jeha_Simplify.simplify
        false
        ctxt
        simp_funs
        given_clause
    fun trace_msg_clauses tracer msg clauses =
      tracer ctxt 
        (fn () => msg ^ JClause.pretty_clauses ctxt clauses)
    val _ = trace_msg_clauses Jeha_Common.trace_msg_simp_results "simplification results:" simplifications
    val _ = trace_msg_clauses Jeha_Common.trace_msg_archive "intermediates " archive;
    (* val _ = Jeha_Common.trace_msg ctxt (K "START REDUNDANCY CHECK") *)
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
            val _ = Jeha_Common.trace_msg ctxt (fn () => "discarding redundant or trivial clause")
          in
            []
          end
        else [clause]
  in
    (* FIXME: Rename "archive" to "intermediate" or "to_archive". *)
    { simplifications = flat (map discard_trivial simplifications), archive = archive }
  end

fun map_filter_partition _ _ [] acc = acc
    (* archive includes in particular deleted actives! *)
  | map_filter_partition ctxt f (x :: xs) (archive, changed, unchanged) =
        case f x of
          (* NOTE: Discarding new_archive, since the active clause was deleted, and we don't need
          the simplification steps that led to deletion for proof reconstruction. *)
          { simplifications = [], archive = new_archive } =>
            map_filter_partition ctxt f xs (x :: archive, changed, unchanged)
        | { simplifications = [y], archive = new_archive } =>
            (* One simplification, check the id to see if it is actually the original clause and no
            simplification was performed. *)
            if JClause.id y <> JClause.id x
              (* id changed, clause was simplified *)
              then map_filter_partition ctxt f xs (new_archive @ archive, y :: changed, unchanged)
              (* clause was not simplified *)
              else
                if null new_archive
                  then map_filter_partition ctxt f xs (archive, changed, y :: unchanged)
                  (* error *)
                  else (
                    let
                      fun trace_msg_clauses tracer msg clauses =
                        tracer ctxt 
                          (fn () => msg ^ JClause.pretty_clauses ctxt clauses)
                      val () = trace_msg_clauses Jeha_Common.trace_msg_backward_simp "active clause, single simplified active" [x,y]
                      val () = Jeha_Common.trace_msg_backward_simp ctxt (fn () =>
                        "with ids: "
                        ^ @{make_string} (JClause.id x)
                        ^ " and "
                        ^ @{make_string} (JClause.id y))
                      val () =
                        trace_msg_clauses
                          Jeha_Common.trace_msg_archive
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
    val active_ids = map JClause.id active
    val simp_ctxt =
      ctxt
      |> Config.map Jeha_Common.trace
        (fn s => s andalso Config.get ctxt Jeha_Common.trace_backward_simp)
    val archive = []
    val simplifications = []
    val { simplifications = rewrite_simplifications, archive = rewrite_archive } =
      backward_rewrite simp_ctxt active green_index given_clause
    val archive = rewrite_archive @ archive 
    val simplifications = rewrite_simplifications @ simplifications
    (* remove archived clauses from active set *)
    (* FIXME: remove deactivated clauses from indices? *)
    val active = filter_out (member (op= o apply2 JClause.id) rewrite_archive) active
    val (archive, simplified_actives, unsimplifiable_actives) =
      map_filter_partition
        ctxt
        (forward_simplify
          simp_ctxt
          { forward = false, cheap = false }
          [given_clause]
          unit_index
          green_index
          subsumption_index)
        active
        (archive, simplifications, [])
    (* FIXME: at this point the active set and its indices are in an unusual state *)
    val subsumed_unsimplifiable_active_ids =
      get_backward_subsumed ctxt given_clause unsimplifiable_actives subsumption_index
    val (subsumed_unsimplifiable_actives, unsimplifiable_actives) =
      List.partition
        (member (op=) subsumed_unsimplifiable_active_ids o JClause.id)
        unsimplifiable_actives
    val archive = subsumed_unsimplifiable_actives @ archive
    val () = \<^assert>
      (subset (op=) (active_ids, map JClause.id archive @ map JClause.id unsimplifiable_actives))
  in
    (archive, simplified_actives, unsimplifiable_actives)
  end

fun infer_clauses ctxt active given_clause green_index =
  let
    (* the equality literals that are being eliminated *)
    val eqs_given : (JClause.T * (JLit.lpos * JClause.cpos)) list =
      map
        (pair given_clause)
        (Jeha_Common.cartesian_product [JLit.Left, JLit.Right] (JClause.cposs_of given_clause))
    val eqs_active : (JClause.T * (JLit.lpos * JClause.cpos)) list =
      maps (fn c =>
          map (pair c) (Jeha_Common.cartesian_product [JLit.Left, JLit.Right] (JClause.cposs_of c)))
        active
    (* what we're superposing into *)
    val targets_given : (JClause.T * JClause.full_pos) list =
      map (pair given_clause) (JClause.green_full_poss_of given_clause)
    val targets_active : (JClause.T * JClause.full_pos) list =
      maps (fn c => map (pair c) (JClause.green_full_poss_of c)) active
    val eq_target_pairs =
      Jeha_Common.cartesian_product eqs_active targets_given
    (* for ERes, EFact *)
    val given_clause_cposs = JClause.cposs_of given_clause
    val given_clause_lpos_cpos_pairs =
      Jeha_Common.cartesian_product [JLit.Left, JLit.Right] given_clause_cposs
    val given_clause_lpos_cpos_pairs_pairs =
      Jeha_Common.cartesian_product
        given_clause_lpos_cpos_pairs
        given_clause_lpos_cpos_pairs
    val all_disabled = Config.get ctxt Jeha_Common.disable_all
    (* val _ = if all_disabled then writeln "ALL DISABLED!!!!" else () *)
    (* a bit contrived to make it lazy *)
    fun if_cfg rule f = if not all_disabled orelse Config.get ctxt rule then f () else []
  in
    []
    @ (if_cfg Jeha_Common.rule_sup (fn _ => sup_given_into_active ctxt given_clause active green_index))
    @ (if_cfg Jeha_Common.rule_sup (fn _ => (maps (uncurry (infer_sup ctxt)) eq_target_pairs)))
    (* ERes, EFact have already been performed for the active clauses *)
    @ (if_cfg Jeha_Common.rule_e_res (fn _ =>
        (maps (infer_eres ctxt given_clause) given_clause_cposs)))
    @ (if_cfg Jeha_Common.rule_e_fact (fn _ =>
        (maps (infer_efact ctxt given_clause) given_clause_lpos_cpos_pairs_pairs)))
    @ (if_cfg Jeha_Common.rule_arg_cong (fn _ =>
        (maps (infer_arg_cong ctxt given_clause) given_clause_cposs)))
    @ (if_cfg Jeha_Common.rule_bool_hoist (fn _ =>
        (maps (infer_bool_hoist ctxt given_clause) (JClause.green_full_poss_of given_clause))))
    @ (if_cfg Jeha_Common.rule_false_elim (fn _ =>
        (maps (infer_false_elim ctxt given_clause) given_clause_lpos_cpos_pairs)))
    @ (if_cfg Jeha_Common.rule_bool_rw (fn _ =>
        (maps (infer_bool_rw ctxt given_clause) (JClause.green_full_poss_of given_clause))))
    @ (if_cfg Jeha_Common.rule_eq_hoist (fn _ =>
        (maps (infer_eq_hoist ctxt given_clause) (JClause.green_full_poss_of given_clause))))
    @ (if_cfg Jeha_Common.rule_neq_hoist (fn _ =>
        (maps (infer_neq_hoist ctxt given_clause) (JClause.green_full_poss_of given_clause))))
    @ (if_cfg Jeha_Common.rule_forall_hoist (fn _ =>
        (maps (infer_forall_hoist ctxt given_clause) (JClause.green_full_poss_of given_clause))))
    @ (if_cfg Jeha_Common.rule_exists_hoist (fn _ =>
        (maps (infer_exists_hoist ctxt given_clause) (JClause.green_full_poss_of given_clause))))
    @ (if_cfg Jeha_Common.rule_forall_rw (fn _ =>
        (maps (infer_forall_rw ctxt given_clause) (JClause.green_full_poss_of given_clause))))
    @ (if_cfg Jeha_Common.rule_exists_rw (fn _ =>
        (maps (infer_exists_rw ctxt given_clause) (JClause.green_full_poss_of given_clause))))
  end

datatype step_result = Unsat | MaybeSat | Next 

type prover_state =
  { context: Proof.context
  , countdown: int
  , passive: Passive_Set.T
  , active: JClause.T list
  , green_index: (int * JClause.full_pos) Term_Index.T
  , unit_index: (int * JLit.lpos) Term_Index.T
  , subsumption_index: Subsumption_Index.index
  , archive: JClause.T list
  }

fun given_clause_step
  { context, countdown, passive, green_index, unit_index, active, subsumption_index, archive }
=
  if countdown <= 0 then error "TIMEOUT" else
  (Runtime.exn_trace (fn () =>
  let
    (* tracing *)
    val _ = Jeha_Common.trace_msg context (fn () => "countdown = " ^ @{make_string} countdown)
    fun trace_msg_clauses tracer msg clauses =
      tracer context
        (fn () => msg ^ JClause.pretty_clauses context clauses)
    val _ =
      let val passive_seq = passive |> seq_of_passive_set in
          trace_msg_clauses
            Jeha_Common.trace_msg_passive
            ("passive [10/" ^ (passive_seq |> Seq.list_of |> length |> @{make_string}) ^ "]")
            (passive_seq |> Seq.take 10 |> Seq.list_of)
      end

    (* FIXME: return MAYBE_SAT (because of incompleteness) if passive set is empty (i.e. no
    inferences are possible and empty clause has not been derived). Later: no non-redundant
    inferences *)
    val (given_clause, passive) = select_given_clause passive

    (* tracing *)
    val _ = trace_msg_clauses Jeha_Common.trace_msg "given_clause " [given_clause]
    val forward_simp_ctxt = context |> (Config.map Jeha_Common.trace (fn s =>
      s andalso Config.get context Jeha_Common.trace_forward_simp))
  in
    (* simplify given_clause with active set *)
    (* FIXME TODO add simplification steps to archive *)
    case
      forward_simplify
        forward_simp_ctxt
        { forward = true, cheap = false }
        active
        unit_index
        green_index
        subsumption_index
        given_clause
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
            , active = empty_clause :: active
            , green_index = green_index
            , unit_index = unit_index
            , subsumption_index = subsumption_index
            , archive = intermediate @ archive } )
      | NONE =>
          let
            val archive = intermediate @ archive
            (* following zipperposition (src/prover/saturate.ml) add all simplifications except one
            (the current given_clause) to the passive set *)
            val passive = add_new_clauses passive simplifications
            (* simplify actives with given clause *)
            (* FIXME: remove direct descendants of redundant_actives and simplified_actives from
            passive set, or: do what's described in the E 2.3 paper (deleting at activation time) *)
            val _ = Jeha_Common.trace_msg_backward_simp context (K "START BACKWARD SIMPLIFICATION")
            val
              ( redundant_active_and_intermediate_simplifications
              , simplified_active
              , unsimplifiable_active )
            =
              backward_simplify context active unit_index green_index subsumption_index given_clause
            val archive = redundant_active_and_intermediate_simplifications @ archive
            (* remove simplified and redundant actives, add given_clause to active set *)
            val active = given_clause :: unsimplifiable_active
            val green_index = Term_Index.insert_clause given_clause green_index
            val unit_index =
              if JClause.is_unit given_clause
                then Term_Index.insert_unit given_clause unit_index
                else unit_index
            val subsumption_index =
              Subsumption_Index.insert_clause given_clause subsumption_index
            (* perform all possible inferences between given_clause and active set NOTE: also
            computes inferences between given_clause and itself! *)
            val _ = Jeha_Common.trace_msg_inferred context (K "START INFERRING NEW CLAUSES")
            val inferred_clauses = infer_clauses context active given_clause green_index
            val _ = trace_msg_clauses Jeha_Common.trace_msg_inferred "inferred: " inferred_clauses
            (* clauses to be added to passive set *)
            val _ = Jeha_Common.trace_msg_cheap_simp context (K "START CHEAP SIMPLIFICATION")
            val { simplifications = new_clauses, intermediate = cheap_simplification_intermediate } =
              fold
                (fn inferred_clause =>
                  fn { simplifications = simplifications, intermediate = intermediate } => 
                    let
                      val { simplifications = new_simplifications, archive = new_intermediate } =
                        (* cheap_simplify *)
                        forward_simplify
                          context
                          { forward = true, cheap = true }
                          active
                          unit_index
                          green_index
                          subsumption_index
                          inferred_clause
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
            val _ = trace_msg_clauses Jeha_Common.trace_msg_cheap_simp "cheap_simplified: " new_clauses
            val _ = if length (filter (not o is_trivial) new_clauses) <> length new_clauses
              then error "assert failed: forward_simplify returned trivial clauses"
              else ()
            val _ = Jeha_Common.trace_msg_cheap_simp context (K "END CHEAP SIMPLIFICATION")
            val _ = trace_msg_clauses Jeha_Common.trace_msg_inferred "new_clauses: " new_clauses
            (* add inferred clauses to passive set *)
            val passive = add_new_clauses passive new_clauses
            (* tracing *)
            val _ = trace_msg_clauses Jeha_Common.trace_msg_active "active: " active
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

exception JEHA_EXCEPTION of exn * prover_state

fun given_clause_loop dump state =
  case (if dump
        then
          (case Exn.capture given_clause_step state of
            Exn.Exn e => raise (JEHA_EXCEPTION (e, state))
          | Exn.Res res => res)
        else given_clause_step state) of
    (Unsat, state) => (Unsat, state)
  | (Next, state) => given_clause_loop dump state

fun try_saturate context prems =
  let
    val _ = Jeha_Common.trace_msg context (fn () =>
      "prems: "
      ^ Jeha_Common.pretty_terms context
          (map (Object_Logic.drop_judgment context o Thm.prop_of) prems))
    fun clause_of_prem prem =
      prem
      |> Thm.prop_of
      |> Object_Logic.drop_judgment context (* remove Trueprop *)
      |> (fn t => JClause.of_term context (t, Clause_Id.new ()))
      |> JClause.set_origin (Jeha_Log.Axiom { thm = prem })
    val clauses = map clause_of_prem prems
    val _ = Jeha_Common.trace_msg context (fn () =>
      "clauses: "
      ^ Jeha_Common.pretty_terms (Jeha_Common.verbose_of context) (map JClause.term_of clauses))
    val _ = Jeha_Common.trace_msg context (fn () => "\n>>> start of given clause procedure <<<")
    val (result, final_state) =
      Runtime.exn_trace (fn () =>
        given_clause_loop
          true
          { context = context
          , countdown = Config.get context Jeha_Common.max_number_of_steps
          , passive = (init_passive_set clauses)
          , active = []
          , green_index = Term_Index.empty
          , unit_index = Term_Index.empty
          , subsumption_index =
              Subsumption_Index.make_index (Subsumption_Index.collect_symbols clauses)
          , archive = [] })
  in
    (result, final_state)
  end

fun make_clause_db state clause_id =
  case
    find_first (fn c => JClause.id c = clause_id) ((#active state) @ (#archive state))
  of
    SOME clause => clause
  | NONE => error ("No clause with id " ^ @{make_string} clause_id ^ " in active set or archive.")

end;
