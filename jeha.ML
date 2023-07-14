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
  val literal_can_match_single_disagreement : Proof.context -> int * JLit.T -> int * JLit.T -> bool
  val equality_subsumes : Proof.context -> JClause.T * JClause.T -> bool
  val bool_rw_non_var_rules : (term * term) list
  (* outer clausification *)
  val outer_clausify : bool -> term -> JClause.T -> JClause.T list
  val simp_bool_outer_claus : JClause.T -> JClause.cpos -> JClause.T list
  val simp_rewrite_positive_lits : Proof.context -> JClause.T * JLit.lpos -> JClause.T * JClause.full_pos -> JClause.T option
  val simp_rewrite_negative_lits : Proof.context -> JClause.T * JLit.lpos -> JClause.T * JClause.full_pos -> JClause.T option
  val infer_eq_neq_outer_claus : JClause.T -> JClause.cpos -> JClause.T list
  val infer_sup : Proof.context -> (JClause.T * (JLit.lpos * JClause.cpos)) -> (JClause.T * JClause.full_pos) -> JClause.T list
  val infer_eres : Proof.context -> JClause.T -> JClause.cpos -> JClause.T list
  val infer_efact : Proof.context -> JClause.T -> ((JLit.lpos * JClause.cpos) * (JLit.lpos * JClause.cpos)) -> JClause.T list
  val infer_arg_cong : Proof.context -> JClause.T -> JClause.cpos -> JClause.T list
  val infer_bool_hoist : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_false_elim : Proof.context -> JClause.T -> (JLit.lpos * JClause.cpos) -> JClause.T list
  val infer_bool_rw : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_eq_hoist : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_neq_hoist : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_forall_hoist : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_exists_hoist : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_forall_rw : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val infer_exists_rw : Proof.context -> JClause.T -> JClause.full_pos -> JClause.T list
  val forward_simplify : Proof.context -> bool -> JClause.T list -> JClause.T -> JClause.T list
  val infer_clauses : Proof.context -> JClause.T list -> JClause.T -> JClause.T list
  (* *)
  structure Passive_Set : HEAP
  val init_passive_set : JClause.T list -> Passive_Set.T
  datatype step_result = Unsat | MaybeSat | Next 
  type prover_state =
    { context: Proof.context
    , countdown: int
    , passive: Passive_Set.T
    , active: JClause.T list
    , archive: JClause.T list
    }
  (* original exception + prover state before the exception was raised *)
  exception JEHA_EXCEPTION of exn * prover_state
  val given_clause_loop : bool -> prover_state -> step_result * prover_state
  val given_clause_step : prover_state -> step_result * prover_state
  val try_saturate : Proof.context -> thm list -> step_result * prover_state
  val make_clause_db : prover_state -> int -> JClause.T
end

structure Jeha : JEHA =
struct

(* oc function from the PhD thesis
logically:
  outer_clausify b s c = clauses of (if b then s else \<not>s) \<or> c
Distribute the first logical symbol (\<and>, \<or>, \<longrightarrow>) over the clause (removing prefix
of negations above and below) *)
(* FIXME: refresh ids *)
fun outer_clausify b (@{term Not} $ s) c = outer_clausify (not b) s c
  | outer_clausify b (Const (@{const_name HOL.disj}, _) $ s $ t) c =
    if b
      then [fold JClause.add_literal [JLit.mk_pred s b, JLit.mk_pred t b] c]
      else
        [ JClause.add_literal (JLit.mk_pred s b) c
        , JClause.add_literal (JLit.mk_pred t b) c
        ]
  | outer_clausify b (Const (@{const_name HOL.conj}, _) $ s $ t) c =
    if b
      then
        [ JClause.add_literal (JLit.mk_pred s b) c
        , JClause.add_literal (JLit.mk_pred t b) c
        ]
      else [fold JClause.add_literal [JLit.mk_pred s b, JLit.mk_pred t b] c]
  | outer_clausify b (Const (@{const_name HOL.implies}, _) $ s $ t) c =
      (* rewrite as disjunction, additional not will be removed in JLit.mk_pred *)
      outer_clausify b (HOLogic.mk_disj (HOLogic.mk_not s, t)) c
  (* FIXME: Making HO Sup work p.7 says: never simplify \<longleftrightarrow>. What does this mean
  concretely? (Isabelle represents \<longleftrightarrow> as HOL.eq) *)
  | outer_clausify b (Const (@{const_name HOL.eq}, _) $ s $ t) c =
      [JClause.add_literal (s, t, b) c]
  (* FIXME: add forall, exists *)
  | outer_clausify b s c = []

(*** Rules ***)
(* rule implementation checklist:
  * conditions checked?
  * requires normalization?
  * 
*)

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
  let
    (* positions of duplicates in the clause, critically in reverse order *)
    val cposs_of_dups =
      fold_index
        (fn (i, l) => fn (dup_is, head_list) =>
          if exists (curry JLit.aconv l) head_list
            (* duplicate of l has already been seen *)
            then (i::dup_is, head_list)
            (* l is new, add it to the seen lits *)
            else (dup_is, l::head_list))
        (JClause.literals c)
        ([], [])
      |> fst
    val c' = fold JClause.delete_lit_at cposs_of_dups c
  in
    if JClause.length c' = JClause.length c
      then NONE
      else
        (Jeha_Common.trace_msg ctxt (fn () =>
          "deleted duplicated literals in " ^ JClause.pretty_clause ctxt c);
        SOME (JClause.refresh_id () c'))
  end

(* Deletion of resolved literals (DR) (Schulz) *)
fun simp_delete_resolved_lits ctxt c =
  let
    (* literal of the from s \<noteq> s *)
    fun is_false_disequation (s, t, is_positive) = not is_positive andalso s aconv t
    val c' = JClause.filter_out_lits is_false_disequation c
  in
    if JClause.length c' = JClause.length c
      then NONE
      else
        (Jeha_Common.trace_msg ctxt (fn () =>
          "deleted resolved literals in " ^ JClause.pretty_clause ctxt c);
        SOME (
          JClause.refresh_id () c'
          |> JClause.set_origin
            (Jeha_Log.DeleteResolvedLits  { premise = JClause.id c })
        ))
  end

fun is_pos_unit { literals = [(_, _, true)], ... } = true
  | is_pos_unit _ = false

(* Rewriting of positive (RP) or negative literals (RN) simplification (Schulz) *)
fun impl_simp_rewrite_lits positive ctxt (unit_clause, lp) (target_clause, j as (_, _, target_cp)) =
  (* check unit_clause *)
  if not (is_pos_unit unit_clause) then NONE else
  (* check that to be rewritten literal is indeed positive / negative *)
  if not (positive = #3 (JClause.lit_at target_cp target_clause)) then NONE else
  let
    (* in particular: ensure the variables of `to` are distinct from those of target_clause *)
    val unit_clause = JClause.incr_indexes (JClause.maxidx target_clause + 1) unit_clause
    val (from, to) = apply2 (JLit.term_at_lpos (the_single (JClause.literals unit_clause))) (lp, JLit.swap_lpos lp) (* Schulz: (s, t) *)
    val target_term = JClause.subterm_at_full_pos target_clause j (* Schulz: u *)
    val matchers =
      Jeha_Unify.matchers
        (Context.Proof ctxt)
        (JClause.maxidx_of2 (unit_clause, target_clause))
        [(from, target_term)]
    fun build_conclusion matcher =
      let
        val msg =  "   " ^ (if positive then "(RP)" else "(RN)")
          ^ " rewriting " ^ Jeha_Common.pretty_term ctxt target_term
          ^ " in " ^ JClause.pretty_clause ctxt target_clause
          ^ " with " ^ Jeha_Common.pretty_term ctxt from
          ^ " \<mapsto> " ^ Jeha_Common.pretty_term ctxt to
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
            |> JClause.norm_beta_eta_qeta
            |> JClause.map_maxidx (K (Envir.maxidx_of matcher))
          val rewriting_clause = JClause.dummy [(from, to, true)]
          val rewriting_smaller_than_rewritten = (fn () =>
            SOME LESS = JClause.kbo (rewriting_clause, rewritten_clause))
        in
          (* FIXME: understand and implement the restrictions on RP form Schulz's paper *)
          (* for RP the rewriting clause must be smaller than the rewritten clause *)
          (* FIXME: is this what that sentence means? Relevant: zipperposition, superposition.ml:1886
          in detail:
          (* Context: c is the to be rewritten clause, t is the literal where the rewrite happens *)
            (* - The rewriting clause is smaller than the rewritten clause *)
          (* Quesiton: does (not toplevel) correspond to Schulz' p \<noteq> \<lambda>? *)
            (not toplevel ||
          (* Question: does this mean "rewritten literal is not strictly maximal?"
          Is this what Schulz calls "not eligible for paramodulation"? *)
            C.lits c |> CCArray.exists (fun lit -> Lit.Seq.terms lit |>
              Iter.exists (fun s -> Comp.is_Gt_or_Geq (O.compare ord s t))) ||
          (* Context: r' is the matching side of the equation (our `to`) with the matcher applied *)
          (* Question: at this point the *)
            C.lits c |> CCArray.exists (fun lit -> match Literal.View.as_eqn lit with
                | Some (litl, litr, true) ->
                  T.equal t litl && Comp.is_Gt_or_Geq (O.compare ord litr r') ||
                  T.equal t litr && Comp.is_Gt_or_Geq (O.compare ord litl r')
                | Some (litl, litr, false) -> T.equal t litl || T.equal t litr
                | None -> false))
          *)
          if positive andalso not (rewriting_smaller_than_rewritten ()) then NONE else
          (Jeha_Common.trace_msg ctxt (fn () => msg);
          (* writeln ("      " ^ (Jeha_Common.pretty_tenv ctxt (Envir.term_env matcher))); *)
          (JClause.norm_beta_eta_qeta rewritten_clause)
          |> JClause.refresh_id ()
          |> SOME)
        end
      end
  in
    matchers
    (* FIXME: print warning message when discarding unifiers? *)
    |> Seq.take 4
    |> Seq.map_filter build_conclusion
    |> Seq.pull
    |> Jeha_Common.map_some #1
  end

(* Rewriting of positive literals (RP) simplification (Schulz) *)
val simp_rewrite_positive_lits = impl_simp_rewrite_lits true

(* Rewriting of positive literals (RN) simplification (Schulz) *)
val simp_rewrite_negative_lits = impl_simp_rewrite_lits false

(* Negative simplify-reflect (NS) simplification (Schulz) *)
fun simp_negative_simplify_reflect ctxt (unit_clause, unit_lp) (target_clause, target_cp) =
  if is_pos_unit unit_clause then NONE else
  (* check that to be deleted literal is indeed positive *)
  if not (true = #3 (JClause.lit_at target_cp target_clause)) then NONE else
  let
    val unit_clause = JClause.incr_indexes (JClause.maxidx target_clause + 1) unit_clause
    val maxidx = JClause.maxidx_of2 (unit_clause, target_clause)
    val unit_lit = the_single (JClause.literals unit_clause) (* Schulz: s, t *)
    val (s, t, false) = JLit.orient unit_lp unit_lit
    val target_lit = JClause.lit_at target_cp target_clause (* Schulz: u[], u[]*)
    val (u, v, b) = target_lit
    val exists_matcher =
      [(u, s), (v, t)]
      |> Jeha_Unify.matchers (Context.Proof ctxt) maxidx
      |> Seq.pull
      |> is_some
    (* tracing *)
    val msg =  "   " ^ "(NS)"
      ^ " deleting " ^ JClause.pretty_clause ctxt (JClause.dummy [target_lit])
      ^ " in " ^ JClause.pretty_clause ctxt target_clause
      ^ " with " ^ JClause.pretty_clause ctxt (JClause.dummy [unit_lit])
  in
    if exists_matcher
      then let val _ = Jeha_Common.trace_msg ctxt (fn () => msg) in
        target_clause
        |> JClause.delete_lit_at target_cp
        |> JClause.refresh_id ()
        |> SOME 
      end
      else NONE
  end

(* given terms s, t, the longest common position p s.t. s, t are equal except
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
    val unit_lit =
      unit_lit |> JLit.map (Logic.incr_indexes ([], [], target_maxidx + 1))
    val maxidx = unit_maxidx + target_maxidx + 1
    val (lhs, rhs, true) = unit_lit (* Schulz: s, t *)
    val (target_lhs, target_rhs, _) = target_lit (* Schulz: u[], u[]*)
    (* Schulz: longest possbile p *)
    val longest_prefix_of_disagreements =
      find_single_green_disagreement ctxt (target_lhs, target_rhs)
    fun can_match_disagreement_position prefix_of_disagreements =
      let
        val (target_term_lhs, target_term_rhs) = (* u|\<^sub>p *)
          (JTerm.subterm_at target_lhs prefix_of_disagreements,
          JTerm.subterm_at target_rhs prefix_of_disagreements)
        val exists_matcher =
          ( [(lhs, target_term_lhs), (rhs, target_term_rhs)]
          , [(lhs, target_term_rhs), (rhs, target_term_lhs)] )
          |> apply2 (Jeha_Unify.matchers (Context.Proof ctxt) maxidx)
          |> Seq.interleave
          |> Seq.pull
          |> is_some
      in
        exists_matcher
      end
  in
      case longest_prefix_of_disagreements of
        NONE => false (* terms are equal, (TD1) or (DR) will take care of it *)
      | SOME longest_prefix_of_disagreements =>
          (* Schulz' p is any of the prefixes of the longest possible p *)
          exists (can_match_disagreement_position) (prefixes longest_prefix_of_disagreements)
  end

(* Positive simplify-reflect (PS) simplification (Schulz)
      s = t    u\<langle>\<sigma>(s)\<rangle>\<^sub>p \<noteq> u\<langle>\<sigma>(t)\<rangle>\<^sub>p \<or> R
      --------------------------------
      s = t              R
*)
fun simp_positive_simplify_reflect ctxt unit_clause (target_clause, target_cp) =
  if not (is_pos_unit unit_clause) then NONE else
  (* check that to be deleted literal is indeed negative *)
  if not (false = #3 (JClause.lit_at target_cp target_clause)) then NONE else
  let
    val lit = the_single (JClause.literals unit_clause) (* Schulz: s, t *)
    val target_lit = JClause.lit_at target_cp target_clause (* Schulz: u[], u[]*)
    val exists_matcher =
      literal_can_match_single_disagreement
        ctxt (JClause.maxidx unit_clause, lit) (JClause.maxidx target_clause, target_lit)
    (* tracing *)
    val msg =  "   " ^ "(PS)"
      ^ " deleting " ^ JClause.pretty_clause ctxt (JClause.dummy [target_lit])
      ^ " in " ^ JClause.pretty_clause ctxt target_clause
      ^ " with " ^ JClause.pretty_clause ctxt (unit_clause)
  in
    if exists_matcher
      then let val _ = Jeha_Common.trace_msg ctxt (fn () => msg) in
        target_clause
        |> JClause.delete_lit_at target_cp
        |> JClause.refresh_id ()
        |> SOME 
      end
      else NONE
  end

(* Equality subsumption (ES) redundancy check (Schulz) *)
fun equality_subsumes ctxt (unit_clause, target_clause) =
  if not (is_pos_unit unit_clause) then false else
  let
    val unit_lit = (JClause.maxidx unit_clause, the_single (JClause.literals unit_clause)) (* Schulz: s, t *)
    val positive_lits = map (pair (JClause.maxidx target_clause)) (filter #3 (JClause.literals target_clause))
    val exists_matcher = exists (literal_can_match_single_disagreement ctxt unit_lit) positive_lits
    val _ = if exists_matcher then Jeha_Common.trace_msg ctxt (fn () =>
      "equality subsumed by " ^ JClause.pretty_clause ctxt unit_clause) else ()
  in
    exists_matcher
  end

fun is_trivial c =
  contains_syntactic_equation (JClause.literals c) orelse contains_syntactic_complementaries (JClause.literals c)

fun is_redundant ctxt active c =
  let fun trace_subsumed unit subsumed =
    subsumed andalso
      (Jeha_Common.trace_msg ctxt (fn () => "subsumed by " ^ JClause.pretty_clause ctxt unit); true)
  in
  (* forward subsumption: does any active clause subsume c? *)
  exists
    (fn ac => equality_subsumes ctxt (ac, c)
      orelse trace_subsumed ac (Jeha_Subsumption.subsumes (Context.Proof ctxt) (ac, c)))
    active
  end

(** Clausification **)

fun is_boolean_const t = t = @{term True} orelse t = @{term False}

fun ml_bool_of @{term True} = true
  | ml_bool_of @{term False} = false
  | ml_bool_of _ = error "term is not HOL.True or HOL.False"

fun hol_bool_of true = @{term "True"}
  | hol_bool_of false = @{term "False"}
  | hol_bool_of _ = error "term is not true of false"

fun is_eq_bool_lit (s, t, true) = exists is_boolean_const [s, t]
    (* FIXME: Maybe accept boolean disequations? (by turning them into equations) *)
  | is_eq_bool_lit _ = false

fun dest_eq_bool_lit (s, t, true) =
  if is_boolean_const t
    then (s, t)
  else if is_boolean_const s
    then (t, s)
  else error "neither is HOL.True or HOL.False"
  (* FIXME: allow disequations? (see similar comment above mk_pred) *)
  | dest_eq_bool_lit _ = error "disequation"

(* PosOuterClaus and NegOuterClaus simplficiations *)
fun simp_bool_outer_claus c i =
  let
    val (s, b) = JClause.lit_at i c |> dest_eq_bool_lit ||> ml_bool_of
    val c' = JClause.delete_lit_at i c
  in
    outer_clausify b s c'
  end

fun find_simp_bool_outer_clause c = error "find_simp_bool_outer_clause unimplemented"

(* EqOuterClaus and NeqOuterClaus inferences *)
fun infer_eq_neq_outer_claus c i =
  let
    val (s, t, b) = JClause.lit_at i c
  in
    if (Runtime.exn_trace (fn () =>
          not (fastype_of s = @{typ bool} andalso fastype_of t = @{typ bool})
    ))
      then error "not boolean equation"
    else if b
      then (* EqOuterClaus *)
        [ fold JClause.add_literal [JLit.mk_pred s false, JLit.mk_pred t true] c
        , fold JClause.add_literal [JLit.mk_pred s true, JLit.mk_pred t false] c
        ]
      else (* NeqOuterClaus *)
        [ fold JClause.add_literal [JLit.mk_pred s false, JLit.mk_pred t false] c
        , fold JClause.add_literal [JLit.mk_pred s true, JLit.mk_pred t true] c
        ]
  end

(*
fun impl_infer_sup precheck ctxt (d, (lp, cp), (c, u_pos)) =
  let
    (* rename *)
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
    val d = JClause.incr_indexes (JClause.maxidx c + 1) d
    val env = Envir.empty (JClause.maxidx_of2 (c, d))
    val rewriting_literal = JClause.lit_at cp d (* t \<approx> t' *)
    val (t, t', is_pos_eq) = JLit.orient lp rewriting_literal
    val u = JClause.subterm_at_full_pos c u_pos
  in
    if not is_pos_eq then [] else
    if JTerm.might_be_fluid u then [] else (* 1. *)
    if is_Var u andalso JClause.occurs_deeply u c then [] else (* 2. *)
    (* FIXME: 3. variable condition ... *)
    let
      val unifiers = Jeha_Unify.smash_unifiers (Context.Proof ctxt) [(t, u)] env
      (* FIXME: print warning message when discarding unifiers *)
      val (unifiers, _) = Seq.chop 4 unifiers
      fun build_conclusion unifier =
        let
          val (c, d) = (c, d) |> apply2 (JClause.norm_beta_eta_qeta_env unifier)
          val u_eligible = JClause.is_eligible_full_pos c u_pos
          (* This checks for strict eligibility of cp because the literal at cp is positive. *)
          val tt'_eligible = JClause.is_eligible_cpos d cp
          val c_comp_d = JClause.kbo (c, d)
          val d' = JClause.delete_lit_at cp d
          (* this relies on normalization not destroying green / top level positions, i.e.
          (t = t')\<sigma> = (t\<sigma> = t'\<sigma>) and C<u>\<sigma> = C\<sigma><u\<sigma>> *)
          val (t, t', _) = JLit.orient lp (JClause.lit_at cp d)
          val ct' = JClause.map_at_full_pos u_pos (K t') c
          val t_comp_t' = Jeha_Order.kbo (t, t')
        in
          (* order restrictions *)
          if SOME LESS = t_comp_t' orelse SOME EQUAL = t_comp_t' then NONE else (* 5. *)
          if not u_eligible then NONE else (* 6. *)
          if SOME LESS = c_comp_d orelse SOME EQUAL = c_comp_d then NONE else (* 7. *)
          if not tt'_eligible then NONE else (* 8. *)
          (* FXIME 9. 10. *)
          JClause.combine d' ct'
          |> JClause.refresh_id ()
          |> JClause.set_origin
              (Jeha_Log.Sup
                { left_premise = JClause.id d
                , right_premise = JClause.id c
                , literal = (lp, cp)
                , subterm = u_pos
                , substitution = unifier })
          |> SOME
        end
    in
      map_filter build_conclusion unifiers
    end
  end

(* ERes inference *)
fun infer_eres (ctxt : Proof.context) c cp =
  let
    val (u, u', is_pos_eq) = JClause.lit_at cp c
    val unifiers = Jeha_Unify.smash_unifiers (Context.Proof ctxt) [(u, u')] (Envir.empty (JClause.maxidx c))
    (* FIXME: print warning message when discarding unifiers *)
    val (unifiers, _) = Seq.chop 4 unifiers
    fun build_conclusion unifier =
      let
        val c = c |> JClause.norm_beta_eta_qeta_env unifier
      in
        if not (JClause.is_eligible_cpos c cp) then NONE else
        c
        |> JClause.delete_lit_at cp
        |> JClause.refresh_id ()
        |> JClause.set_origin (Jeha_Log.ERes { premise = JClause.id c, literal = cp, substitution = unifier })
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
    val (u', v', is_pos') = JLit.orient lp' (JClause.lit_at cp' c)
    val (u, v, is_pos) = JLit.orient lp (JClause.lit_at cp c)
    val unifiers = Jeha_Unify.smash_unifiers (Context.Proof ctxt) [(u, u')] (Envir.empty (JClause.maxidx c))
    (* FIXME: print warning message when discarding unifiers *)
    val (unifiers, _) = Seq.chop 4 unifiers
    fun build_conclusion unifier =
      let
        val c = c |> JClause.norm_beta_eta_qeta_env unifier
        val (u', v', _) = JLit.orient lp' (JClause.lit_at cp' c)
        val uv_literal = JClause.lit_at cp c
        val (u, v, _) = JLit.orient lp uv_literal
        val u_v_comp = Jeha_Order.kbo (u, v)
        val uv_maximal = Jeha_Order.is_maximal JLit.kbo false uv_literal (JClause.literals c)
      in
        if SOME EQUAL = u_v_comp orelse SOME LESS = u_v_comp then NONE else
        if not uv_maximal then NONE else
        (* FIXME: nothing is selected in C condition *)
        c
        |> JClause.delete_lit_at (Int.max (cp, cp'))
        |> JClause.delete_lit_at (Int.min (cp, cp'))
        |> JClause.add_literal (v, v', false)
        |> JClause.add_literal (u, v', true)
        |> JClause.refresh_id ()
        |> JClause.set_origin
            (Jeha_Log.EFact
              { premise = JClause.id c
              , left_literal = (lp', cp')
              , right_literal = (lp, cp)
              , substitution = unifier })
        |> SOME
      end
    in
      if not (is_pos andalso is_pos') then [] else
      if cp' = cp then [] else
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
          |> JClause.map_at_cpos cpos (K new_literal)
          |> JClause.norm_beta_eta_qeta_env unifier
          |> JClause.map_maxidx (K new_maxidx)
          |> JClause.refresh_id ()
          |> JClause.set_origin
              (Jeha_Log.ArgCong 
                { premise = JClause.id c, literal = cpos, number_of_vars = length fresh_variables })
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
          |> JClause.map_at_full_pos u_pos (K @{term "HOL.False"})
          |> JClause.add_literal u_eq_true
          |> JClause.norm_beta_eta_qeta_env unifier
          |> JClause.refresh_id ()
          |> JClause.set_origin (Jeha_Log.BoolHoist { premise = JClause.id c, subterm = u_pos, substitution = unifier })
          |> single
        end
  in
    (build_conclusion () handle TUNIFY => [])
  end

(* FIXME: apply as simplification if unifier is the identity *)
fun infer_false_elim ctxt c (lp, cp) =
  let
    val (s, s', b) = JClause.lit_at cp c |> JLit.orient lp
    val unifiers = if not b then Seq.empty else
      Jeha_Unify.smash_unifiers
        (Context.Proof ctxt)
        [(s, @{term "False"}), (s', @{term "True"})]
        (Envir.empty (JClause.maxidx c))
    (* FIXME: print warning message when discarding unifiers *)
    val (unifiers, _) = Seq.chop 4 unifiers
    fun build_conclusion unifier =
      let
        val c = c |> JClause.norm_beta_eta_qeta_env unifier
      in
        if not (JClause.is_eligible_cpos c cp) then NONE else (* 2. *)
        c
        |> JClause.delete_lit_at cp
        |> JClause.refresh_id ()
        |> JClause.set_origin (Jeha_Log.FalseElim { premise = JClause.id c, literal = (lp, cp), substitution = unifier })
        |> SOME
      end
  in
    map_filter build_conclusion unifiers
  end

val bool_rw_non_var_rules =
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
      [ (HOLogic.mk_conj, ml_conj)
      , (HOLogic.mk_disj, ml_disj)
      , (HOLogic.mk_imp, ml_imp) ]
  end

(* Implementation of BoolRw, EqHoist, NeqHoist, ForallHoist and ExistsHoist.
unifies u with boolean pattern, returns C<\<top>> or C<\<bottom>> and checks relevant conditions *)
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
    val maxidx = Int.max (Int.max (JClause.maxidx c, maxidx_of_term pattern), the_default ~1 (Jeha_Common.map_some JLit.maxidx_of disjunct_with))
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
    (* FIXME: print warning message when discarding unifiers? *)
    val (unifiers, _) = Seq.chop 4 unifiers
    fun build_conclusion unifier =
      let
        val c = c |> JClause.norm_beta_eta_qeta_env unifier
        val new_literal =
          Jeha_Common.map_some
            (JLit.map (JTerm.norm_beta_eta_qeta_env unifier))
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

        val maxidx = Int.max (Int.max (JClause.maxidx c, maxidx_of_term insert_for_u), the_default ~1 (Jeha_Common.map_some JLit.maxidx_of new_literal))
      in
        (* 3. the position of u is eligible in C w.r.t. \<sigma> *)
        if not (JClause.is_eligible_full_pos c u_pos) then NONE else
        (* 4. if the head of u is a variable ... *)
        if not u_variable_headed_condition then NONE else

        c
        |> JClause.map_at_full_pos u_pos (K insert_for_u)
        |> JClause.map_maxidx (K maxidx)
        (* add the new literal if it exists, otherwise apply identity function *)
        |> the_default I (Jeha_Common.map_some JClause.add_literal new_literal)
        |> JClause.refresh_id ()
        |> pair unifier
        |> SOME
      end
  in
    map_filter build_conclusion unifiers
  end
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
      bool_rw_non_var_rules
    fun apply_rw_rule (t, t') =
      impl_infer_bool_rw_eq_neq_fa_ex_hoist ctxt c u_pos t false t' NONE
      |> map (fn (unifier, clause) => clause |> JClause.set_origin (Jeha_Log.BoolRw { premise = JClause.id c, subterm = u_pos, subrule = (t, t'), substitution = unifier }))
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
    val fresh_typ = TVar (("'a", maxidx + 1), Sign.defaultS (Proof_Context.theory_of ctxt))
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
          { premise = JClause.id c, subterm = u_pos, substitution = unifier }))
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
  in
      impl_infer_bool_rw_eq_neq_fa_ex_hoist ctxt clause u_pos pattern false insert_for_u NONE
      |> map (fn (unifier, clause) => clause |> JClause.set_origin (
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
fun forward_simplify ctxt cheap active given_clause =
  let
    val do_trace = Config.get ctxt Jeha_Common.trace
    val ctxt = Config.put Jeha_Common.trace (do_trace andalso not cheap) ctxt (* don't trace cheap simplify *)
    val active_units = Seq.filter (fn c => JClause.length c = 1) (Seq.of_list active)
    val active_units_all_orientations : (JClause.T * JLit.lpos) Seq.seq =
      Jeha_Common.seq_cartesian_product active_units (Seq.of_list [JLit.Left, JLit.Right])
    val rn_rp_rules = Seq.of_list [simp_rewrite_negative_lits, simp_rewrite_positive_lits]
    fun first_successful_rewrite c =
      let
        val green_targets : (JClause.T * JClause.full_pos) Seq.seq = Seq.map (pair c) (Seq.of_list (JClause.green_full_poss_of c))
        val unit_target_pairs = Jeha_Common.seq_cartesian_product active_units_all_orientations green_targets
        (* successful rewrites of c (NONE filtered out) *)
        val rn_rp_rewrites : JClause.T Seq.seq =
          Jeha_Common.seq_cartesian_product rn_rp_rules unit_target_pairs
          |> Seq.map_filter (fn (rule, (unit, target)) => rule ctxt unit target)
        val ps_rewrites : JClause.T Seq.seq =
          Jeha_Common.seq_cartesian_product active_units (Seq.map (pair c) (Seq.of_list (0 upto (length (JClause.literals c) - 1))))
          |> Seq.map_filter (fn (unit, target) => simp_positive_simplify_reflect ctxt unit target)
        val ns_rewrites : JClause.T Seq.seq =
          Jeha_Common.seq_cartesian_product active_units_all_orientations (Seq.map (pair c) (Seq.of_list (0 upto (length (JClause.literals c) - 1))))
          |> Seq.map_filter (fn (oriented_unit, target) => simp_negative_simplify_reflect ctxt oriented_unit target)
        val dd_dr_rewrites : JClause.T Seq.seq =
            Seq.map_filter (fn f => f c) (Seq.of_list [simp_delete_duplicated_lits ctxt, simp_delete_resolved_lits ctxt])
      in
        (* following Schulz: RN, RP, PS, NS, DD, DR *)
        Seq.empty
        |> (Seq.append rn_rp_rewrites
          o Seq.append (if not cheap then ps_rewrites else Seq.empty)
          o Seq.append (if not cheap then ns_rewrites else Seq.empty)
          o Seq.append dd_dr_rewrites)
        |> Seq.pull
        |> Jeha_Common.map_some #1
      end
    (* rewrite until not possible anymore *)
    (* FIXME: can this lead to a fixed-point (and not terminate)? No, even RP with unit s\<approx>t and \<sigma> a
    unifier of s and t as well, violates s\<sigma> > t\<sigma>*)
    fun full_rewrite c countdown =
      if countdown = 0 then let val _ = writeln "full_rewrite countdown reached" in c end else
      (* let val _ = Jeha_Common.trace_msg ctxt (fn () => (if cheap then "cheap " else "") ^ "rewrite step of " ^ JClause.pretty_clause ctxt c ^ ":") in *)
      case first_successful_rewrite c of
        SOME c' =>
          full_rewrite c' (countdown - 1)
      | NONE =>
          let val _ = Jeha_Common.trace_msg ctxt (fn () => "done rewriting " ^ JClause.pretty_clause ctxt c ^ ".") in
          c
          end
      (* end *)
    val given_clause = full_rewrite given_clause 10
  in
    if
      is_redundant ctxt active given_clause
      (* FIXME: this is not specified in the E paper, so should we perform inferences with tautologies?? *)
      orelse is_trivial given_clause
        then
          let val _ = Jeha_Common.trace_msg ctxt (fn () => "discarding redundant or trivial given_clause") in
          []
          end
        else [given_clause]
  end
  (* let
    val idxs = find_simp_bool_outer_clause given_clause
    val outer_clausified = flat (map (simp_bool_outer_claus given_clause) idxs)
  in
    outer_clausified
  end *)

fun map_filter_partition _ [] = ([], [], [])
  | map_filter_partition f (x :: xs) =
      let
        val (deleted, changed, unchanged) = map_filter_partition f xs
      in
        case f x of
          [y] =>
            if JClause.id y = JClause.id x
              then (deleted, changed, y :: unchanged)
              else (deleted, y :: changed, unchanged)
        | [] => (x :: deleted, changed, unchanged)
      end

fun backward_simplify ctxt active given_clause =
  map_filter_partition (forward_simplify (Config.put Jeha_Common.trace false ctxt) false [given_clause]) active

fun infer_clauses ctxt active given_clause =
  let
    (* the equality literals that are being eliminated *)
    val eqs_given : (JClause.T * (JLit.lpos * JClause.cpos)) list =
      map (pair given_clause) (Jeha_Common.cartesian_product [JLit.Left, JLit.Right] (JClause.cposs_of given_clause))
    val eqs_active : (JClause.T * (JLit.lpos * JClause.cpos)) list =
      maps (fn c => map (pair c) (Jeha_Common.cartesian_product [JLit.Left, JLit.Right] (JClause.cposs_of c))) active
    (* what we're superposing into *)
    val targets_given : (JClause.T * JClause.full_pos) list =
      map (pair given_clause) (JClause.green_full_poss_of given_clause)
    val targets_active : (JClause.T * JClause.full_pos) list =
      maps (fn c => map (pair c) (JClause.green_full_poss_of c)) active
    val eq_target_pairs =
      Jeha_Common.cartesian_product eqs_given targets_active @ Jeha_Common.cartesian_product eqs_active targets_given
    (* for ERes, EFact *)
    val given_clause_cposs = JClause.cposs_of given_clause
    val given_clause_lpos_cpos_pairs = Jeha_Common.cartesian_product [JLit.Left, JLit.Right] given_clause_cposs
    val given_clause_lpos_cpos_pairs_pairs =
      Jeha_Common.cartesian_product
        given_clause_lpos_cpos_pairs
        given_clause_lpos_cpos_pairs
  in
    maps (uncurry (infer_sup ctxt)) eq_target_pairs
    (* ERes, EFact have already been performed for the active clauses *)
    @ maps (infer_eres ctxt given_clause) given_clause_cposs
    @ maps (infer_efact ctxt given_clause) given_clause_lpos_cpos_pairs_pairs
    @ maps (infer_arg_cong ctxt given_clause) given_clause_cposs
    @ maps (infer_bool_hoist ctxt given_clause) (JClause.green_full_poss_of given_clause)
    @ maps (infer_false_elim ctxt given_clause) given_clause_lpos_cpos_pairs
    @ maps (infer_bool_rw ctxt given_clause) (JClause.green_full_poss_of given_clause)
    @ maps (infer_eq_hoist ctxt given_clause) (JClause.green_full_poss_of given_clause)
    @ maps (infer_neq_hoist ctxt given_clause) (JClause.green_full_poss_of given_clause)
    @ maps (infer_forall_hoist ctxt given_clause) (JClause.green_full_poss_of given_clause)
    @ maps (infer_exists_hoist ctxt given_clause) (JClause.green_full_poss_of given_clause)
    @ maps (infer_forall_rw ctxt given_clause) (JClause.green_full_poss_of given_clause)
    @ maps (infer_exists_rw ctxt given_clause) (JClause.green_full_poss_of given_clause)
  end

datatype step_result = Unsat | MaybeSat | Next 

type prover_state =
  { context: Proof.context
  , countdown: int
  , passive: Passive_Set.T
  , active: JClause.T list
  , archive: JClause.T list
  }

fun given_clause_step { context, countdown, passive, active, archive } =
  if countdown <= 0 then error "TIMEOUT" else
  (Runtime.exn_trace (fn () =>
  let
    (* tracing *)
    val _ = Jeha_Common.trace_msg context (fn () => "countdown = " ^ @{make_string} countdown)
    fun trace_msg_clauses msg clauses =
      Jeha_Common.trace_msg context
        (fn () => msg ^ JClause.pretty_clauses context clauses)
    val _ =
      let val passive_seq = passive |> seq_of_passive_set in
          trace_msg_clauses
            ("passive [10/" ^ (passive_seq |> Seq.list_of |> length |> @{make_string}) ^ "]")
            (passive_seq |> Seq.take 10 |> Seq.list_of)
      end

    (* FIXME: return MAYBE_SAT (because of incompleteness) if passive set is empty (i.e. no
    inferences are possible and empty clause has not been derived). Later: no non-redundant
    inferences *)
    val (given_clause, passive) = select_given_clause passive

    (* tracing *)
    val _ = trace_msg_clauses "given_clause " [given_clause]
  in
    (* simplify given_clause with active set *)
    (* FIXME TODO add simplification steps to archive *)
    case forward_simplify context false active given_clause of
      (* given_clause redundant w.r.t. active set *)
      [] => (Next, { context = context, countdown = countdown - 1, passive = passive, active = active, archive = archive })
      (* select first simplification as given_clause *)
    | given_clause :: simplifications =>
      (* if given_clause simplifies to (or is) [] then UNSAT *)
      case find_first JClause.is_false (given_clause :: simplifications) of
        SOME empty_clause =>
          (Unsat, { context = context, countdown = countdown - 1, passive = passive, active = empty_clause :: active , archive = archive })
      | NONE =>
          let
            (* following zipperposition (src/prover/saturate.ml) add all simplifications except one
            (the current given_clause) to the passive set *)
            val passive = add_new_clauses passive simplifications
            (* simplify actives with given clause *)
            (* FIXME: remove direct descendants of redundant_actives and simplified_actives from
            passive set, or: do what's described in the E 2.3 paper (deleting at activation time) *)
            val (redundant_active, simplified_active, unsimplifiable_active) =
              backward_simplify context active given_clause
            val archive = redundant_active @ archive
            (* remove simplified and redundant actives, add given_cluase to active set *)
            val active = given_clause :: unsimplifiable_active
            (* perform all possible inferences between given_clause and active set NOTE: also
            computes inferences between given_clause and itself! *)
            val inferred_clauses = infer_clauses context active given_clause
            (* val _ = trace_msg_clauses "inferred: " inferred_clauses *)
            (* clauses to be added to passive set *)
            val new_clauses =
              simplified_active @ inferred_clauses
              (* cheap_simplify *)
              |> maps (forward_simplify context true active)
              (* |> (fn cheap_simplified => (trace_msg_clauses "cheap_simplified: " cheap_simplified; cheap_simplified)) *)
              |> filter (not o is_trivial)
            val _ = trace_msg_clauses "new_clauses: " new_clauses
            (* add inferred clauses to passive set *)
            val passive = add_new_clauses passive new_clauses
            (* tracing *)
            val _ = trace_msg_clauses "active: " active
          in
            (Next, { context = context, countdown = countdown - 1, passive = passive, active = active, archive = archive })
          end
  end
  ))

exception JEHA_EXCEPTION of exn * prover_state

fun given_clause_loop dump state =
  case (if dump
        then
          given_clause_step state
            handle e => raise (JEHA_EXCEPTION
              (e, state)
            )
        else given_clause_step state) of
    (Unsat, state) => (Unsat, state)
  | (Next, state) => given_clause_loop dump state

fun try_saturate context prems =
  let
    val _ = Jeha_Common.trace_msg context
      (fn () => "prems: " ^ Jeha_Common.pretty_terms context (map (Object_Logic.drop_judgment context o Thm.prop_of) prems))
    fun clause_of_prem prem =
      prem
      |> Thm.prop_of
      |> Object_Logic.drop_judgment context (* remove Trueprop *)
      |> (fn t => JClause.of_term (t, Clause_Id.new ()))
      |> JClause.set_origin (Jeha_Log.Axiom { thm = prem })
    val clauses = map clause_of_prem prems
    val _ = Jeha_Common.trace_msg context (fn () => "clauses: " ^ Jeha_Common.pretty_terms (Jeha_Common.verbose_of context) (map JClause.term_of clauses))
    val _ = Jeha_Common.trace_msg context (fn () => "\n>>> start of given clause procedure <<<")
    val (result, final_state) =
      Runtime.exn_trace (fn () =>
        given_clause_loop
          true
          { context = context, countdown = 300, passive = (init_passive_set clauses), active = [], archive = [] }
      )
  in
    (result, final_state)
  end

fun make_clause_db state clause_id =
  (* FIXME include archive *)
  let
    val SOME clause = find_first (JClause.id #> curry (op =) clause_id) (#active state)
  in
    clause
  end

(*
Question:

f x y         f(x, y)

  $              f
 /|\      or    / \    ?
f x y          x   y
(HO)            (FO)

  / \
 $
/ \
f  x

x is green. What about f itself?

green part:
  $
  |\
  x y

nongreen leaves:
   
 /  
f    

FIXME: f x is a subterm

Counter argument:
o\<lambda>Sup paper, below Definition 6:
  "[...] or has an argument of the form \<lambda>x. v such that x occurs free in a nongreen position of v."

consider v = f x y

If the term f x is in a nongreen position f x y then x occurs in a nongreen position subterm of v. x also
occurs in a green position of v.

But if we take v = f y x then x occurs only in green positions of v.

If however f x is not a subterm of f x y at all, this ambiguity disappears.

Proposed Definitions:
* variadic application (/combination) with function as it's first child and arguments as the rest
* term positions: standard definition of position in a tree
* green positions as in paper
* nongreen positions are all the other positions

Observation:
* The whole tree is green.
* Every suffix of a green position is a green position.
=> The green positions span a subtree starting at the root.




*)
end;
