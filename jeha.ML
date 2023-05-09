(*

general procedure:

1. Q\<^sub>\<approx> normalize
2. \<beta>\<eta>Q\<^sub>\<eta>-normalize
3. 

*)

signature JEHA =
sig
  (* outer clausification *)
  val outer_clausify : bool -> term -> JClause.T -> JClause.T list
  val simp_bool_outer_claus : JClause.T -> JClause.cpos -> JClause.T list
  val simp_rewrite_positive_lits : Proof.context -> JClause.T * JLit.lpos -> JClause.T * JClause.full_pos -> JClause.T option
  val simp_rewrite_negative_lits : Proof.context -> JClause.T * JLit.lpos -> JClause.T * JClause.full_pos -> JClause.T option
  val infer_eq_neq_outer_claus : JClause.T -> JClause.cpos -> JClause.T list
  val infer_sup : Proof.context -> (JClause.T * (JLit.lpos * JClause.cpos)) -> (JClause.T * JClause.full_pos) -> JClause.T list
  val infer_eres : Proof.context -> (JClause.T * JClause.cpos) -> JClause.T list
  val forward_simplify : Proof.context -> bool -> JClause.T list -> JClause.T -> JClause.T list
  val infer_clauses : Proof.context -> JClause.T list -> JClause.T -> JClause.T list
  (* *)
  structure Passive_Set : HEAP
  val passive_set_of_list : JClause.T list -> Passive_Set.T
  type loopstate
  (* original exception + prover state before the exception was raised *)
  exception JEHA_EXCEPTION of exn * (Proof.context * int * Passive_Set.T * JClause.T list)
  val given_clause_loop : bool -> Proof.context -> int -> Passive_Set.T -> JClause.T list -> string
  val given_clause_step : Proof.context -> int -> Passive_Set.T -> JClause.T list -> loopstate
  val refutable : Proof.context -> thm list -> cterm list -> term -> bool
end

structure Jeha : JEHA =
struct

(* cartesian_product : 'a list -> 'b list -> ('a * 'b) list *)
fun cartesian_product [] _ = []
  | cartesian_product (x :: xs) ys = map (pair x) ys @ cartesian_product xs ys

fun seq_cartesian_product xs ys =
  case Seq.pull xs of
    SOME (x, xs) => Seq.append (Seq.map (pair x) ys) (seq_cartesian_product xs ys)
  | NONE => Seq.empty

fun map_some _ NONE = NONE
  | map_some f (SOME x) = SOME (f x)

(* oc function from the paper
logically: outer_clausify b s c = clauses of (if b then s else \<not>s) \<or> c
Distribute the first logical symbol (\<and>, \<or>, \<longrightarrow>) over the clause (removing prefix of negations
above and below) *)
(* FIXME: Implement as specified in PhD thesis. *)
(* FIXME: Making HO Sup work p.7 says: never simplify \<longleftrightarrow>. What does this mean concretely? (Isabelle
represents \<longleftrightarrow> as HOL.eq) *)
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
  | outer_clausify b s c = [JClause.add_literal (JLit.mk_pred s b) c]

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
        SOME (JClause.refresh_id () c'))
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
            SOME LESS = Jeha_Order.clause_kbo (rewriting_clause, rewritten_clause))
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
          SOME (JClause.norm_beta_eta_qeta rewritten_clause))
        end
      end
  in
    matchers
    (* FIXME: print warning message when discarding unifiers? *)
    |> Seq.take 4
    |> Seq.map_filter build_conclusion
    |> Seq.pull
    |> map_some #1
  end

(* Rewriting of positive literals (RP) simplification (Schulz) *)
val simp_rewrite_positive_lits = impl_simp_rewrite_lits true

(* Rewriting of positive literals (RN) simplification (Schulz) *)
val simp_rewrite_negative_lits = impl_simp_rewrite_lits false

(* Negative simplify-reflect (NS) simplification (Schulz) *)
fun simp_negative_simplify_reflect ctxt unit_clause (target_clause, target_cp) =
  if is_pos_unit unit_clause then NONE else
  (* check that to be deleted literal is indeed positive *)
  if not (true = #3 (JClause.lit_at target_cp target_clause)) then NONE else
  let
    val unit_clause = JClause.incr_indexes (JClause.maxidx target_clause + 1) unit_clause
    val maxidx = JClause.maxidx_of2 (unit_clause, target_clause)
    val lit = the_single (JClause.literals unit_clause) (* Schulz: s, t *)
    val target_lit = JClause.lit_at target_cp target_clause (* Schulz: u[], u[]*)
    val lit_as_positive = let val (s, t, false) = lit in (s, t, true) end
    val exists_matcher =
      (target_lit, lit_as_positive)
      |> Jeha_Subsumption.literal_matchers ctxt maxidx
      |> Seq.pull
      |> is_some
    (* tracing *)
    val msg =  "   " ^ "(NS)"
      ^ " deleting " ^ JClause.pretty_clause ctxt (JClause.dummy [target_lit])
      ^ " in " ^ JClause.pretty_clause ctxt target_clause
      ^ " with " ^ JClause.pretty_clause ctxt (JClause.dummy [lit])
  in
    if exists_matcher
      then let val _ = Jeha_Common.trace_msg ctxt (fn () => msg) in
        SOME (JClause.delete_lit_at target_cp target_clause)
      end
      else NONE
  end

(* given terms s, t, find a common position p s.t. s, t only disagree at p *)
(* FIXME: rename to find_single_blue_disagreement and change appropriately *)
(* FIXME: how to deal with types??? Right now we're only considering variables instantiated by the
unifier. Does well-typedness of the literal tell us enough to make this work? *)
fun find_single_green_disagreement ctxt term_pair : JTerm.tpos =
  (* 1. Find a unifier.
     2. Find the position of all variables affected by the unifier.
     3. Their longest common prefix is the single disagreement *)
  let
    (* FIXME: maybe it's possible to easily deal with flex-flex pairs here *)
    val unifiers = Jeha_Unify.smash_unifiers (Context.Proof ctxt) [term_pair] Envir.init
  in
    case Seq.pull unifiers of
      NONE => [] (* \<epsilon> *)
    | SOME (env, _) => 
        (* FIXME: Check that this works with triangular form unifiers. I would guess not because
        later variables refer to r.h.s. of previous instantiations. *)
        let
          val affected_vars = Vartab.keys (Envir.term_env env)
          fun term_poss_of_affected_vars t =
            (* consider all positions in the term *)
            JTerm.green_tposs_of t
            (* filter out the ones that don't point to affected variables *)
            |> filter (fn tp =>
                case JTerm.subterm_at t tp of
                  Var (x, _) => exists (curry (op =) x) affected_vars
                | _ => false)
        in
          term_pair
          |> apply2 term_poss_of_affected_vars
          |> (op @)
          |> foldr1 (fst o chop_common_prefix (op =)) handle List.Empty => [] (* \<epsilon> *)
        end
  end

(* implementation of positive simplify-reflect and equality subsumption *)
fun literal_can_match_single_disagreement ctxt (unit_maxidx, unit_lit) (target_maxidx, target_lit) =
  let
    val unit_lit = JLit.map (Logic.incr_indexes ([], [], target_maxidx + 1)) unit_lit
    val maxidx = unit_maxidx + target_maxidx + 1
    val (lhs, rhs, true) = unit_lit (* Schulz: s, t *)
    val (target_lhs, target_rhs, _) = target_lit (* Schulz: u[], u[]*)
    (* Schulz: p *)
    val single_disagreement_position = find_single_green_disagreement ctxt (target_lhs, target_rhs)
    val (target_term_lhs, target_term_rhs) = (* u|\<^sub>p *)
      (JTerm.subterm_at target_lhs single_disagreement_position,
      JTerm.subterm_at target_rhs single_disagreement_position)
    (* FIXME: does matching need renaming or not? *)
    val exists_matcher =
      (Jeha_Unify.matchers (Context.Proof ctxt) maxidx ([(lhs, target_term_lhs), (rhs, target_term_rhs)]),
      Jeha_Unify.matchers (Context.Proof ctxt) maxidx ([(lhs, target_term_rhs), (rhs, target_term_lhs)]))
      |> Seq.interleave
      |> Seq.pull
      |> is_some
  in
    exists_matcher
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
    val exists_matcher = literal_can_match_single_disagreement ctxt (JClause.maxidx unit_clause, lit) (JClause.maxidx target_clause, target_lit)
    (* tracing *)
    val msg =  "   " ^ "(PS)"
      ^ " deleting " ^ JClause.pretty_clause ctxt (JClause.dummy [target_lit])
      ^ " in " ^ JClause.pretty_clause ctxt target_clause
      ^ " with " ^ JClause.pretty_clause ctxt (unit_clause)
  in
    if exists_matcher
      then let val _ = Jeha_Common.trace_msg ctxt (fn () => msg) in
        SOME (JClause.delete_lit_at target_cp target_clause)
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
      orelse trace_subsumed ac (Jeha_Subsumption.subsumes ctxt (ac, c)))
    active
  end

(** Clausification **)

fun is_boolean_const t = t = @{term True} orelse t = @{term False}

fun ml_bool_of @{term True} = true
  | ml_bool_of @{term False} = false
  | ml_bool_of _ = error "term is not HOL.True or HOL.False"

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
    if not (fastype_of s = @{typ bool} andalso fastype_of t = @{typ bool})
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

(* Sup inference *)
fun infer_sup ctxt (d, i as (lp, cp)) (c, j) =
  let
    (* FIXME: better renaming strategy: collect Vars from one term in a Vars structure
    (term_item.ML), traverse the other creating an environment mapping names already used to fresh
    names
    ALSO: Only make t and u (and compose environments afterwards? Envir.merge?)
    OR: try to use Envir.empty max_idx (augment clauses with max_idx?) and Envir.genvar
    SEE: COMP_INCR maybe?
    NOTE: how to handle TVars? *)
    val d = JClause.incr_indexes (JClause.maxidx c + 1) d
    val env = Envir.empty (JClause.maxidx_of2 (c, d))
    val (_, _, is_pos_eq) = JClause.lit_at cp d
    val t = JClause.subterm_at_full_pos d ([], lp, cp)
    val t' = JClause.subterm_at_full_pos d ([], JLit.swap_lpos lp, cp)
    val u = JClause.subterm_at_full_pos c j
  in
    if
      not is_pos_eq orelse
      JTerm.might_be_fluid u orelse
      (is_Var u andalso JClause.occurs_deeply u c)
    then []
    else
      (* FIXME: Is smash_unifiers the one we want? How lossy is this? *)
      (* FIXME: Later, try to keep around flex-flex pairs for a while? *)
      let
        val unifiers = Jeha_Unify.smash_unifiers (Context.Proof ctxt) [(t, u)] env
        (* FIXME: print warning message when discarding unifiers *)
        val (unifiers, _) = Seq.chop 4 unifiers
        fun build_conclusion unifier =
          let
            val d' = JClause.delete_lit_at cp d
            val ct' = JClause.map_at_full_pos j (K t') c
          in
            (* writeln (Jeha_Common.pretty_tenv ctxt (Envir.term_env unifier)); *)
            JClause.combine d' ct'
            |> JClause.norm_beta_eta_qeta_env unifier
            |> JClause.refresh_id ()
          end
      in
        map build_conclusion unifiers
      end
  end

(* ERes inference *)
fun infer_eres (ctxt : Proof.context) ((c, cp) : (JClause.T * JClause.cpos)) =
  let
    val (u, u', is_pos_eq) = JClause.lit_at cp c
    val unifiers = Jeha_Unify.smash_unifiers (Context.Proof ctxt) [(u, u')] (Envir.empty (JClause.maxidx c))
    (* FIXME: print warning message when discarding unifiers *)
    val (unifiers, _) = Seq.chop 4 unifiers
    fun build_conclusion unifier =
      c
      |> JClause.delete_lit_at cp
      |> JClause.norm_beta_eta_qeta_env unifier
      |> JClause.refresh_id ()
  in
    if is_pos_eq
      then []
      else map build_conclusion unifiers
  end

(** Saturation Loop **)

(* Passive_Set *)

fun size_of_clause c =
  fold (fn (l, r, _) => fn acc => acc + size_of_term l + size_of_term r) (JClause.literals c) 0

val size_ord = make_ord (fn (c, d) => size_of_clause c <= size_of_clause d)

(* FIXME: Heap recomputes size (maybe `type elem = int * clause`?) *)
structure Passive_Set = Heap(type elem = JClause.T val ord = size_ord)

fun seq_of_passive_set passive =
  if Passive_Set.is_empty passive
    then Seq.empty
    else Passive_Set.min_elem passive ||> seq_of_passive_set |> uncurry Seq.cons

fun passive_set_of_list clauses = fold Passive_Set.insert clauses Passive_Set.empty

fun add_new_clauses passive clauses = fold Passive_Set.insert clauses passive

fun select_given_clause cs = Passive_Set.min_elem cs

(* FIXME: make sure to include given_clause itself in simplificatons unless it's redundant *)
fun forward_simplify ctxt cheap active given_clause =
  let
    val do_trace = Config.get ctxt Jeha_Common.trace
    val ctxt = Config.put Jeha_Common.trace (do_trace andalso not cheap) ctxt (* don't trace cheap simplify *)
    val active_units = Seq.filter (fn c => JClause.length c = 1) (Seq.of_list active)
    val active_units_all_orientations : (JClause.T * JLit.lpos) Seq.seq =
      seq_cartesian_product active_units (Seq.of_list [JLit.Left, JLit.Right])
    val rn_rp_rules = Seq.of_list [simp_rewrite_negative_lits, simp_rewrite_positive_lits]
    fun first_successful_rewrite c =
      let
        val green_targets : (JClause.T * JClause.full_pos) Seq.seq = Seq.map (pair c) (Seq.of_list (JClause.green_full_poss_of c))
        val unit_target_pairs = seq_cartesian_product active_units_all_orientations green_targets
        (* successful rewrites of c (NONE filtered out) *)
        val rn_rp_rewrites : JClause.T Seq.seq =
          seq_cartesian_product rn_rp_rules unit_target_pairs
          |> Seq.map_filter (fn (rule, (unit, target)) => rule ctxt unit target) 
        val ps_rewrites : JClause.T Seq.seq =
          seq_cartesian_product active_units (Seq.map (pair c) (Seq.of_list (0 upto (length (JClause.literals c) - 1))))
          |> Seq.map_filter (fn (unit, target) => simp_positive_simplify_reflect ctxt unit target)
        val ns_rewrites : JClause.T Seq.seq =
          seq_cartesian_product active_units (Seq.map (pair c) (Seq.of_list (0 upto (length (JClause.literals c) - 1))))
          |> Seq.map_filter (fn (unit, target) => simp_negative_simplify_reflect ctxt unit target)
        val dd_dr_rewrites : JClause.T Seq.seq =
            Seq.map_filter (fn f => f c) (Seq.of_list [simp_delete_duplicated_lits ctxt, simp_delete_resolved_lits ctxt])
      in 
        (* following Schulz: RN, RP, PS, FIXME: NS, DD, DR *)
        Seq.empty
        |> (Seq.append rn_rp_rewrites
          o Seq.append (if not cheap then ps_rewrites else Seq.empty)
          o Seq.append (if not cheap then ns_rewrites else Seq.empty)
          o Seq.append dd_dr_rewrites)
        |> Seq.pull
        |> map_some #1
      end
    (* rewrite until not possible anymore *)
    (* FIXME: can this lead to a fixed-point (and not terminate)? *)
    fun full_rewrite c countdown =
      if countdown = 0 then let val _ = writeln "full_rewrite countdown reached" in c end else
      let val _ = Jeha_Common.trace_msg ctxt (fn () => "rewrite step of " ^ JClause.pretty_clause ctxt c ^ ":") in
      case first_successful_rewrite c of
        SOME c' =>
          full_rewrite c' (countdown - 1)
      | NONE =>
          let val _ = Jeha_Common.trace_msg ctxt (fn () => "done rewriting " ^ JClause.pretty_clause ctxt c ^ ".") in
          c
          end
      end
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

fun map_filter_partition f [] = ([], [], [])
  | map_filter_partition f (x :: xs) =
      let
        val (deleted, changed, unchanged) = map_filter_partition f xs
      in
        case f x of
          [y] =>
            (* FIXME: aconv w.r.t. Var and TVar? *)
            if y = x
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
      map (pair given_clause) (cartesian_product [JLit.Left, JLit.Right] (JClause.cposs_of given_clause))
    val eqs_active : (JClause.T * (JLit.lpos * JClause.cpos)) list =
      maps (fn c => map (pair c) (cartesian_product [JLit.Left, JLit.Right] (JClause.cposs_of c))) active
    (* what we're superposing into *)
    val targets_given : (JClause.T * JClause.full_pos) list =
      map (pair given_clause) (JClause.green_full_poss_of given_clause)
    val targets_active : (JClause.T * JClause.full_pos) list =
      maps (fn c => map (pair c) (JClause.green_full_poss_of c)) active
    val eq_target_pairs =
      cartesian_product eqs_given targets_active @ cartesian_product eqs_active targets_given
  in
    maps (uncurry (infer_sup ctxt)) eq_target_pairs
    (* ERes has already been performed for the active clauses *)
    @ maps (infer_eres ctxt) (map (pair given_clause) (0 upto (length (JClause.literals given_clause) - 1)))
  end

datatype loopstate = Unsat | Next of Passive_Set.T * JClause.T list

type prover_state = { context: Proof.context, countdown: int, passive: Passive_Set.T, active: JClause.T list}

fun given_clause_step ctxt countdown passive active =
  if countdown <= 0 then error "TIMEOUT" else
  let
    (* tracing *)
    val _ = Jeha_Common.trace_msg ctxt (fn () => "countdown = " ^ @{make_string} countdown)
    fun trace_msg_clauses msg clauses =
      Jeha_Common.trace_msg ctxt
        (fn () => msg ^ JClause.pretty_clauses ctxt clauses)
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
    val _ = trace_msg_clauses "active: " active
    val _ = trace_msg_clauses "given_clause " [given_clause]
  in
    (* simplify given_clause with active set *)
    case forward_simplify ctxt false active given_clause of
      (* given_clause redundant w.r.t. active set *)
      [] => Next (passive, active)
      (* select first simplification as given_clause *)
    | given_clause :: simplifications => 
      (* if given_clause simplifies to (or is) [] then UNSAT *)
      if exists (curry (op =) [] o JClause.literals) (given_clause :: simplifications)
        then Unsat
        else
          let
            (* following zipperposition (src/prover/saturate.ml) add all simplifications except one
            (the current given_clause) to the passive set *)
            val passive = add_new_clauses passive simplifications
            (* simplify actives with given clause *)
            (* FIXME: remove direct descendants of redundant_actives and simplified_actives from
            passive set, or: do what's described in the E 2.3 paper (deleting at activation time) *)
            val (redundant_active, simplified_active, unsimplifiable_active) =
              backward_simplify ctxt active given_clause
            (* remove simplified and redundant actives, add given_cluase to active set *)
            val active = given_clause :: unsimplifiable_active
            (* perform all possible inferences between given_clause and active set NOTE: also
            computes inferences between given_clause and itself! *)
            val inferred_clauses = infer_clauses ctxt active given_clause
            (* val _ = trace_msg_clauses "inferred: " inferred_clauses *)
            (* clauses to be added to passive set *)
            val new_clauses =
              simplified_active @ inferred_clauses
              (* cheap_simplify *)
              |> maps (forward_simplify ctxt true active)
              (* |> (fn cheap_simplified => (trace_msg_clauses "cheap_simplified: " cheap_simplified; cheap_simplified)) *)
              |> filter (not o is_trivial)
            (* val _ = trace_msg_clauses "new_clauses: " new_clauses *)
            (* add inferred clauses to passive set *)
            val passive = add_new_clauses passive new_clauses
          in
            Next (passive, active)
          end
  end

exception JEHA_EXCEPTION of exn * (Proof.context * int * Passive_Set.T * JClause.T list)

fun given_clause_loop dump ctxt countdown passive active =
  case (if dump
        then
          given_clause_step ctxt countdown passive active
            handle e => raise (JEHA_EXCEPTION (e, (ctxt, countdown, passive, active)))
        else given_clause_step ctxt countdown passive active) of
    Unsat => "UNSAT"
  | Next (passive, active) => given_clause_loop dump ctxt (countdown - 1) passive active

fun refutable ctxt prems asms conjecture =
  let
    val _ = Jeha_Common.trace_msg ctxt
      (fn () => "conjecture: " ^ Jeha_Common.pretty_term ctxt conjecture)
    val prems = map (Object_Logic.atomize_term ctxt o Thm.prop_of) prems
    val _ = Jeha_Common.trace_msg ctxt
      (fn () => "prems: " ^ Jeha_Common.pretty_terms ctxt prems)
    val asms = map (Object_Logic.atomize_term ctxt o Thm.term_of) asms
    val _ = Jeha_Common.trace_msg ctxt
      (fn () => "asms: " ^ Jeha_Common.pretty_terms ctxt asms)
    val neg_conjecture = HOLogic.mk_not (Object_Logic.atomize_term ctxt conjecture)
    val clauses = map_index (fn (_, t) => JClause.of_term (t, Clause_Id.new ())) (neg_conjecture :: asms @ prems)
    val _ = Jeha_Common.trace_msg ctxt (fn () => "clauses: " ^ Jeha_Common.pretty_terms (Jeha_Common.verbose_of ctxt) (map JClause.term_of clauses))
    val _ = Jeha_Common.trace_msg ctxt (fn () => "\n>>> start of given clause procedure <<<")
    val result = given_clause_loop true ctxt 40 (passive_set_of_list clauses) []
  in
    if result = "UNSAT" then true else error result
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
