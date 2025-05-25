(* detailed proof and proof reconstruction *) 
signature JEHA_PROOF =
sig
  (* type proof_step *)
  (* val hol_thm_of_clause : Proof.context -> (int -> JClause.T) -> int -> thm *)
  (* elaborates a \<lambda>oSup inference into a series of more smaller proof steps *)
  (* val fun proof_steps_of_inference : Jeha_Log.inference -> proof_step *)

  val reconstruct : Proof.context -> (int -> JClause.T) -> int -> thm

  (* for testing and debugging *)
  val prepare_forall_exists_hoist_log:
    Proof.context
    -> (int -> JClause.T)
    (* args of Jeha_Log.ForallHoist and Jeha_Log.ExistsHoist *)
    -> {fresh_x: term, substitution: Envir.env, subterm: JClause.full_pos, uninstantiated_premise: int}
    -> {fresh_x: cterm, predicate: cterm, subterm: JClause.full_pos, uninstantiated_premise: JClause.T}
  val impl_forall_exists_hoist_lemma: bool -> { fresh_x: cterm, predicate: cterm } -> thm
  (* The records are modelled after those in Jeha_Log, but with int replace by HClause.htm *)
  val reconstruct_arg_cong :
    Proof.context
    -> { premise: HClause.hthm, literal: JClause_Pos.cpos, vars: term list }
    -> HClause.hthm
  val reconstruct_sup:
    Proof.context
    -> { left_premise: HClause.hthm
       , literal: JLit.lpos * JClause.cpos
       , right_premise: HClause.hthm
       , subterm: JClause.full_pos }
    -> HClause.hthm
  val reconstruct_efact:
    { premise: HClause.hthm
    , left_literal: JLit.lpos * JClause.cpos
    , right_literal: JLit.lpos * JClause.cpos }
    -> HClause.hthm
  val reconstruct_eres: { premise: HClause.hthm, literal: JClause.cpos } -> HClause.hthm
  val reconstruct_false_elim:
    Proof.context
    -> { premise: HClause.hthm, literal: JLit.lpos * JClause.cpos }
    -> HClause.hthm
  val reconstruct_bool_hoist:
    Proof.context
    -> { premise: HClause.hthm, subterm: JClause.full_pos }
    -> HClause.hthm
  val reconstruct_eq_hoist:
    Proof.context
    -> { premise: HClause.hthm, subterm: JClause.full_pos }
    -> HClause.hthm
  val reconstruct_neq_hoist:
    Proof.context
    -> { premise: HClause.hthm, subterm: JClause.full_pos }
    -> HClause.hthm
  val reconstruct_forall_hoist:
    Proof.context
    -> { premise: HClause.hthm, subterm: JClause.full_pos, fresh_x: cterm, predicate: cterm }
    -> HClause.hthm
  val reconstruct_exists_hoist:
    Proof.context
    -> { premise: HClause.hthm, subterm: JClause.full_pos, fresh_x: cterm, predicate: cterm }
    -> HClause.hthm
  val reconstruct_bool_rw:
    Proof.context
    -> { premise: HClause.hthm, subterm: JClause.full_pos, instantiated_subrule: HClause.hthm }
    -> HClause.hthm
  val reconstruct_forall_rw:
    Proof.context
    -> { premise: HClause.hthm, subterm: JClause.full_pos, predicate: term, skolems: (term * term * term) list }
    -> HClause.hthm
  val reconstruct_exists_rw:
    Proof.context
    -> { premise: HClause.hthm, subterm: JClause.full_pos, predicate: term, skolems: (term * term * term) list }
    -> HClause.hthm
  val reconstruct_delete_duplicated_lits:
    { premise: HClause.hthm
    , duplicate_cposs: { duplicate: JClause.cpos, duplicate_of: JClause.cpos, orientation: JLit.lpos } list }
    -> HClause.hthm
  val reconstruct_delete_resolved_lits:
    { premise: HClause.hthm
    , cposs: JClause.cpos list }
    -> HClause.hthm
  val reconstruct_positive_simplify_reflect:
    Proof.context 
    -> { unit: HClause.hthm
       , unit_orientation: JLit.lpos
       , right_premise: HClause.hthm
       , disagreement: JClause.full_pos }
    -> HClause.hthm
  val reconstruct_negative_simplify_reflect:
    Proof.context 
    -> { unit: HClause.hthm
       , unit_orientation: JLit.lpos
       , right_premise: HClause.hthm
       , literal: JClause.cpos }
    -> HClause.hthm
  val reconstruct_simp_outer_claus:
    Proof.context
    -> { premise: HClause.hthm
       , literal: JClause.cpos }
    -> HClause.hthm list
  val reconstruct_neg_ext:
    Proof.context
    -> { premise: HClause.hthm
       , literal: JClause.cpos
       , skolems: (term * term * term) list }
    -> HClause.hthm
end;

structure Jeha_Proof : JEHA_PROOF =
struct

(* Needs to match (HClause.hol_of_clause o JClause.of_term) *)
fun hclause_of_axiom ctxt axiom =
  let
    val axiom_not = axiom COMP @{thm cnf.clause2raw_notE}
    fun REPEAT_DETERM_ALL tac = REPEAT_DETERM (SOMEGOAL (REPEAT_DETERM o tac));
    val eq_to_eq_tac = resolve_tac ctxt [@{lemma "x = y \<Longrightarrow> x = y" by auto}]
    val neq_to_neq_tac = resolve_tac ctxt [@{lemma "x \<noteq> y \<Longrightarrow> x \<noteq> y" by auto}]
    val not_to_eq_false_tac = resolve_tac ctxt [@{lemma "A \<noteq> True \<Longrightarrow> \<not>A" by auto}]
    val yes_to_eq_true_tac = resolve_tac ctxt [@{lemma "A \<noteq> False \<Longrightarrow> A" by auto}]
    val pred_to_negated_lit_tac =
      FIRST' [eq_to_eq_tac, neq_to_neq_tac, not_to_eq_false_tac, yes_to_eq_true_tac]
    val disj_tac =
      (* print_tac ctxt "A"
      THEN *) REPEAT_DETERM (SOMEGOAL (resolve_tac ctxt @{thms cnf.clause2raw_not_disj}))
      (* THEN print_tac ctxt "B" *)
      (* THEN (fn th => (writeln (@{make_string} th); Seq.single th)) *)
      THEN REPEAT_DETERM (SOMEGOAL (resolve_tac ctxt @{thms HOL.cnf.clause2raw_not_not}))
      (* THEN print_tac ctxt "C" *)
      THEN ALLGOALS (pred_to_negated_lit_tac)
      (* THEN print_tac ctxt "D" *)
    val axiom_clausified = Seq.hd (Jeha_Proof_Util.with_all_vars_fixed ctxt disj_tac axiom_not)
  in
    HClause.of_lemma axiom_clausified
  end

val excluded_middle =  @{lemma "P \<Longrightarrow> \<not> P \<Longrightarrow> False" by (rule notE)}

fun reconstruct_arg_cong_one_var ctxt var premise =
  let
    val (s, s', true) = HClause.dest_lit_cterm_at 0 premise
    val T = Thm.ctyp_of_cterm var
    val rT = s |> Thm.ctyp_of_cterm |> Thm.dest_ctyp1 
    val lemma = \<^instantiate>\<open>s and s' and x=var and 'a=T and 'b=rT in
      lemma \<open>(s :: 'a \<Rightarrow> 'b) x \<noteq> s' x \<Longrightarrow> s \<noteq> s'\<close> by auto\<close>
  in
    (* FIXME: skolems *)
    HClause.map_hthm (Jeha_Proof_Util.comp_no_flatten_no_incr (lemma, 1) 1) premise
  end

fun reconstruct_arg_cong ctxt { premise, literal, vars } =
  let
    val premise = HClause.move_from_to literal 0 premise
  in
    fold (reconstruct_arg_cong_one_var ctxt) (map (Thm.cterm_of ctxt) vars) premise
    |> HClause.move_from_to 0 literal
  end

(* \<not> is to be viewed as a metafunction, i.e. \<not>D' is not a proper term but a list of assumptions:

\<not>D' \<Longrightarrow> t /\<approx> t' \<Longrightarrow> False   \<not>C\<langle>t\<rangle>\<^sub>p \<Longrightarrow> False
-------------------------------------------- GroundSup
         \<not>D' \<Longrightarrow> \<not>C\<langle>t'\<rangle>\<^sub>p \<Longrightarrow> False
*)
fun reconstruct_sup
  ctxt
  { left_premise: HClause.hthm
  , right_premise: HClause.hthm
  , literal = (literal_orientation, clause_position)
  , subterm = subterm_position }
=
  let
    (* \<not>D' \<Longrightarrow> t \<approx> t' *)
    val notD'_imp_t_eq_t' =
      left_premise
      |> HClause.make_last clause_position
      |> HClause.negate_head ctxt
      (* FIXME: Use HClause.orient_lit_at before negate_head. *)
      |> HClause.map_hthm (HClause.orient_positive_consequent_lit literal_orientation)
    (* val () = writeln ("\<not>D' \<Longrightarrow> t \<approx> t' :" ^ @{make_string} notD'_imp_t_eq_t') *)
    val (t, t') =
      notD'_imp_t_eq_t'
      |> HClause.thm_of
      |> Thm.concl_of
      |> HOLogic.dest_Trueprop
      |> HOLogic.dest_eq
    
    (* val () = writeln ("\<not>C \<Longrightarrow> False : " ^ @{make_string} right_premise) *)
    (* t = t' \<Longrightarrow> \<not>C\<langle>t'\<rangle>\<^sub>p \<Longrightarrow> False *)
    val t_eq_t'_imp_Ct' =
      HClause.congruence_wrt_subterm_position ctxt (t, t') right_premise subterm_position
    (* val () = writeln ("t = t' \<Longrightarrow> \<not>C\<langle>t'\<rangle>\<^sub>p \<Longrightarrow> False : " ^ @{make_string} t_eq_t'_imp_Ct') *)

    val length_of_D' = HClause.nprems_of notD'_imp_t_eq_t'

    (* \<not>D' \<Longrightarrow> \<not>C t' \<Longrightarrow> False *)
    val notD'_imp_Ct': HClause.hthm =
      HClause.comp_no_flatten_no_incr
        (notD'_imp_t_eq_t', length_of_D') 1 t_eq_t'_imp_Ct'
    (* val () = writeln ("\<not>D' \<Longrightarrow> \<not>C t' \<Longrightarrow> False : " ^ @{make_string} notD'_imp_Ct') *)
  in
    notD'_imp_Ct'
  end

(*
\<not>C' \<Longrightarrow> u=u \<Longrightarrow> False
--------------------- ERes
    \<not>C' \<Longrightarrow> False
*)
fun reconstruct_eres {premise, literal} =
  let
    val (u, _, false) = HClause.dest_lit_cterm_at literal premise
    val uT = Thm.ctyp_of_cterm u
  in
    HClause.compose
    ( \<^instantiate>\<open>u=u and 'a=uT in lemma \<open>(u :: 'a) = u\<close> by auto\<close>
    , literal + 1 (* convert JClause.cpos to 1-based *)
    , premise )
  end

(*
\<not>C' \<Longrightarrow> u /\<approx> v' \<Longrightarrow> u /\<approx> v \<Longrightarrow> False
------------------------------------- EFact
\<not>C' \<Longrightarrow> v \<approx> v' \<Longrightarrow> u /\<approx> v' \<Longrightarrow> False
*)
fun reconstruct_efact {premise, left_literal, right_literal} =
  (* Premise *)
  (* u /\<approx> v' \<Longrightarrow> u /\<approx> v \<Longrightarrow> False *)
  (* Conclusion *)
  (* u /\<approx> v' \<Longrightarrow> v \<approx> v' \<Longrightarrow> False *)

  (* Rewriting clause: *)
  (* \<not>C' \<Longrightarrow> u /\<approx> v' \<Longrightarrow> u \<approx> v *)    (* make_last of premise *)
  (* Lemma: *)
  (* u /\<approx> v' \<Longrightarrow> u \<approx> v' \<Longrightarrow> False *)
  (*              ^-rewrite here   *)
  (* Result *)
  (* \<not>C' \<Longrightarrow> u /\<approx> v' \<Longrightarrow> u /\<approx> v' \<Longrightarrow> v \<approx> v' \<Longrightarrow> False *)
  (* To remove double literal *)
    (* Lemma *)
    (* (A \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False) \<Longrightarrow> (A \<Longrightarrow> B \<Longrightarrow> False) *)
    (* Drule.compose ? FIXME: ??? *)
  let
    (* left_literal and right_literal refer to the rule in the paper, not to how they are actually
    ordered in the premise. *)
    val () = \<^assert> ((snd left_literal : JClause.cpos) <> snd right_literal)
    val premise =
      premise
      |> HClause.orient_lit_at left_literal
      |> HClause.orient_lit_at right_literal
    val (_, [u, v]) =
      premise
      |> HClause.negated_lit_trueprop_cterm_at (snd right_literal)
      |> Thm.dest_arg (* dest_Trueprop *)
      |> Thm.dest_arg (* strip negation *)
      |> Drule.strip_comb
    val (_, [_, v']) =
      premise
      |> HClause.negated_lit_trueprop_cterm_at (snd left_literal)
      |> Thm.dest_arg (* dest_Trueprop *)
      |> Thm.dest_arg (* strip negation *)
      |> Drule.strip_comb
    val left_literal_cpos = snd left_literal
    val right_literal_cpos = snd right_literal
    val left_literal_left_of_right_literal_in_premise = left_literal_cpos < right_literal_cpos
    val C =
      premise
      |> HClause.make_last left_literal_cpos
      |> HClause.make_last (
          right_literal_cpos
          (* Moving a list element past another (to the right) decrements the latter's index. *)
          + (if left_literal_left_of_right_literal_in_premise then ~1 else 0))
    val length_of_C' = HClause.nprems_of premise - 2
    val uT = Thm.ctyp_of_cterm u
    val lemma = \<^instantiate>\<open>u=u and v=v and v'=v' and 'a = uT in
      lemma \<open>((u :: 'a) \<noteq> v' \<Longrightarrow> u \<noteq> v \<Longrightarrow> False) \<Longrightarrow> v = v' \<Longrightarrow> u \<noteq> v' \<Longrightarrow> False\<close>
      by auto\<close>
  in
    HClause.comp_no_flatten (C, length_of_C') 1 (HClause.of_lemma lemma)
  end

fun reconstruct_false_elim ctxt { premise, literal } =
  (* \<not>C' \<Longrightarrow> \<bottom> \<noteq> \<top> \<Longrightarrow> False *)
  (* \<not>C' \<Longrightarrow> \<bottom> \<approx> \<top> *)            (* make_last of premise *)
  (* Lemma *)
  (* \<bottom> \<approx> \<top> \<Longrightarrow> False *)
  (* Drule.comp_no_flatten *)
  (* \<not>C' \<Longrightarrow> False *)
  let
    val C = premise
      |> HClause.orient_lit_at literal
      |> HClause.make_last (snd literal)
      |> HClause.negate_head ctxt
  in
    HClause.comp_no_flatten
      (C, HClause.nprems_of C)
      1
      (HClause.of_lemma @{lemma \<open>False = True \<Longrightarrow> False\<close> by auto})
  end

fun reconstruct_bool_hoist ctxt { premise, subterm = subterm_position } =
  let
    val subterm =
      HClause.green_subterm_at_full_pos (HClause.hterm_of premise) subterm_position
      |> Thm.cterm_of ctxt
    val lemma = \<^instantiate>\<open>x=subterm in lemma \<open>x \<noteq> True \<Longrightarrow> x \<noteq> False \<Longrightarrow> False\<close> by auto\<close>
    val conclusion_from_sup =
      reconstruct_sup
        ctxt
        { left_premise = HClause.of_lemma lemma
        , literal = (JLit.Left, 1)
        , right_premise = premise
        , subterm = subterm_position }
  in
    HClause.make_last 0 conclusion_from_sup
  end

fun reconstruct_eq_hoist ctxt { premise, subterm = subterm_position } =
  let
    val (x, y) =
      HClause.green_subterm_at_full_pos (HClause.hterm_of premise) subterm_position
      |> HOLogic.dest_eq
      |> apply2 (Thm.cterm_of ctxt)
    val T = Thm.ctyp_of_cterm x
    val lemma = \<^instantiate>\<open>x=x and y=y and 'a=T in lemma \<open>(x :: 'a) \<noteq> y \<Longrightarrow> (x = y) \<noteq> False \<Longrightarrow> False\<close> by auto\<close>
    val conclusion_from_sup =
      reconstruct_sup
        ctxt
        { left_premise = HClause.of_lemma lemma
        , literal = (JLit.Left, 1)
        , right_premise = premise
        , subterm = subterm_position }
  in
    HClause.make_last 0 conclusion_from_sup
  end

fun reconstruct_neq_hoist ctxt { premise, subterm = subterm_position } =
  let
    val (x, y) =
      HClause.green_subterm_at_full_pos (HClause.hterm_of premise) subterm_position
      |> snd o dest_comb (* remove \<not> *)
      |> HOLogic.dest_eq
      |> apply2 (Thm.cterm_of ctxt)
    val T = Thm.ctyp_of_cterm x
    val lemma = \<^instantiate>\<open>x=x and y=y and 'a=T in lemma \<open>(x :: 'a) \<noteq> y \<Longrightarrow> (x \<noteq> y) \<noteq> True \<Longrightarrow> False\<close> by auto\<close>
    val conclusion_from_sup =
      reconstruct_sup
        ctxt
        { left_premise = HClause.of_lemma lemma
        , literal = (JLit.Left, 1)
        , right_premise = premise
        , subterm = subterm_position }
  in
    HClause.make_last 0 conclusion_from_sup
  end

(* fun forall_rw_lemma ctxt t =
  let
    val thm = @{thm "verit_sko_forall"}
    val ct = Thm.cterm_of ctxt t
    val instsT = Thm.ctyp_of ctxt (fastype_of t)
    val insts = error ""
    val instantiated = Thm.instantiate (TVars.make instsT, Vars.make insts) thm
  in
    error "unimplemented"
  end *)

(* Extract the required information from the JClause. Reason for the separation is to make
reconstruct_forall_hoist testable without having to create a JClause, substituion etc. *)
fun prepare_forall_exists_hoist_log
  ctxt
  clause_db
  (* Args of Jeha_Log.ForallHoist and Jeha_Log.ExistsHoist *)
  { uninstantiated_premise = uninstantiated_premise, subterm = subterm, substitution = substitution, fresh_x = fresh_x }
=
  let
    (* This shouldn't do anything except for changing the type, s.t. it is compatible in the
    application y\<sigma> x. But does it do that? If so, why? Answer: Yes, because the type of y
    contains the TVar used in the creation of x. *)
    val x = JTerm.norm_beta_eta_qeta_env substitution fresh_x
    val x = Thm.cterm_of ctxt x

    val uninstantiated_premise = clause_db uninstantiated_premise
    val (quantifier $ predicate_variable) = JClause.subterm_at_full_pos uninstantiated_premise subterm
    val () = \<^assert> (JTerm.is_quantifier quantifier)
    val predicate = JTerm.norm_beta_eta_qeta_env substitution predicate_variable
    val predicate = Thm.cterm_of ctxt predicate
  in
    { uninstantiated_premise = uninstantiated_premise
    , subterm = subterm
    , fresh_x = x
    , predicate = predicate }
  end

fun impl_forall_exists_hoist_lemma
  is_forall_hoist
  { fresh_x, predicate }
=
  let
    (* Only the instantiation of the type is strictly necessary, as the fresh variable will remain
    unchanged in the conclusion (except for its type). *)
    val T = Thm.ctyp_of_cterm fresh_x
    val _ = writeln (@{make_string} T) (* FIXME remove *)
    (* val _ = Jeha_Common.trace_msg ctxt (fn () => "forall_rw_lemma: P = " ^ Jeha_Common.pretty_term ctxt predicate)
    val _ = Jeha_Common.trace_msg ctxt (fn () => "forall_rw_lemma: typ_of_x = " ^ Jeha_Common.pretty_typ ctxt (fastype_of fresh_x)) *)
    val lemma =
      if is_forall_hoist then
        (* Alternative:
        [Thm.instantiate'
          [SOME typ_of_x]
          [SOME P, SOME cx]
          @{lemma \<open>P (x :: 'b) = False \<Longrightarrow> (\<forall>x. P x) = True \<Longrightarrow> False\<close> by auto}]
        *)
        \<^instantiate>\<open>
            'T=T and y=predicate and x=fresh_x in
            lemma (open) \<open>y (x :: 'T) \<noteq> True \<Longrightarrow> (\<forall>x. y x) \<noteq> False \<Longrightarrow> False\<close> by auto\<close>
      else
        \<^instantiate>\<open>
            'T=T and y=predicate and x=fresh_x in
            lemma (open) \<open>y (x :: 'T) \<noteq> False \<Longrightarrow> (\<exists>x. y x) \<noteq> True \<Longrightarrow> False\<close> by auto\<close>
    in
      lemma
  end

(* fun forall_hoist_lemma ctxt clause_db (Jeha_Log.ForallHoist args) =
  impl_forall_exists_hoist_lemma ctxt clause_db true args

fun exists_hoist_lemma ctxt clause_db (Jeha_Log.ExistsHoist args) =
  impl_forall_exists_hoist_lemma ctxt clause_db false args *)

fun impl_reconstruct_forall_exists_hoist
  is_forall_hoist
  ctxt
  { premise, subterm = subterm_position, fresh_x, predicate }
=
  let
    val lemma =
      impl_forall_exists_hoist_lemma is_forall_hoist { fresh_x = fresh_x , predicate = predicate }
    val conclusion_from_sup =
      reconstruct_sup
        ctxt
        { left_premise = HClause.of_lemma lemma
        , literal = (JLit.Left, 1)
        , right_premise = premise
        , subterm = subterm_position }
    val conclusion_rotated = HClause.make_last 0 conclusion_from_sup
  in
    conclusion_rotated
  end

val reconstruct_forall_hoist = impl_reconstruct_forall_exists_hoist true

val reconstruct_exists_hoist = impl_reconstruct_forall_exists_hoist false

(* Note: subrule has to be proved and instantiated (like premise). *)
fun reconstruct_bool_rw ctxt { premise, subterm, instantiated_subrule } =
  let
    val conclusion_from_sup =
      reconstruct_sup
        ctxt
        { left_premise = instantiated_subrule
        , literal = (JLit.Left, 0)
        , right_premise = premise
        , subterm = subterm }
  in
    conclusion_from_sup
  end

fun prepare_forall_exists_rw_log
  clause_db
  (* Args of Jeha_Log.ForallRw and Jeha_Log.ExistsRw *)
  { uninstantiated_premise = uninstantiated_premise, subterm = subterm, substitution = substitution, skolems = skolems }
=
  let
    val uninstantiated_premise = clause_db uninstantiated_premise
    val (quantifier $ predicate_variable) = JClause.subterm_at_full_pos uninstantiated_premise subterm
    val () = \<^assert> (JTerm.is_quantifier quantifier)
    val predicate = JTerm.norm_beta_eta_qeta_env substitution predicate_variable
  in
    { uninstantiated_premise = uninstantiated_premise
    , subterm = subterm
    , predicate = predicate
    , skolems = skolems }
  end

fun impl_reconstruct_forall_exists_rw
  is_forall_rw
  ctxt
  { premise, subterm = subterm_position, predicate, skolems }
=
  let
    val [(skolem_const, skolem_with_args, skolem_def)] = skolems
    val lemma: HClause.hthm =
      (* FIXME: move construction of HClause.hthm into forall_exists_rw_lemma function *)
      { th =
          Jeha_Lemma.forall_exists_rw_lemma
            ctxt
            predicate
            is_forall_rw
            (skolem_const, skolem_with_args, skolem_def)
      , skolems = [(skolem_const, skolem_def)]
      }
    val conclusion_from_sup =
      reconstruct_sup
        ctxt
        { left_premise = lemma
        , literal = (JLit.Left, 0)
        , right_premise = premise
        , subterm = subterm_position }
  in
    conclusion_from_sup
  end

val reconstruct_forall_rw = impl_reconstruct_forall_exists_rw true

val reconstruct_exists_rw = impl_reconstruct_forall_exists_rw false

fun impl_delete_duplicated_lit {duplicate, duplicate_of, orientation} premise =
  let
    val () = \<^assert> (duplicate_of < duplicate)
  in
    premise
    |> HClause.orient_lit_at (orientation, duplicate)
    |> HClause.make_last duplicate
    |> HClause.make_last duplicate_of
    |> HClause.merge_duplicated_lit_last
    |> HClause.move_last_to duplicate_of
  end

fun reconstruct_delete_duplicated_lits { premise, duplicate_cposs } =
  let
    (* jeha.ML already guarantees this, just to be safe *)
    val sorted = sort (rev_order o int_ord o apply2 #duplicate) duplicate_cposs
  in
    fold impl_delete_duplicated_lit sorted premise
  end

fun impl_delete_resolved_lit literal premise =
  reconstruct_eres { premise = premise, literal = literal }

fun reconstruct_delete_resolved_lits { premise, cposs } =
  let
    (* VERY IMPORTANT, not as above *)
    val sorted = sort (rev_order o int_ord) cposs
  in
    fold impl_delete_resolved_lit sorted premise
  end

fun reconstruct_positive_simplify_reflect
  ctxt
  { unit, unit_orientation, right_premise, disagreement }
=
  let
     val with_resolved_literal =
       reconstruct_sup
         ctxt
         { left_premise = unit
         , right_premise = right_premise
         , literal = (unit_orientation, 0)
         , subterm = disagreement }
  in
   reconstruct_delete_resolved_lits
     { premise = with_resolved_literal 
     , cposs = [#3 disagreement] }
  end

fun reconstruct_negative_simplify_reflect
  ctxt
  { unit, unit_orientation, right_premise, literal }
=
  let
    (* We're using right_premise to rewrite unit, to obtain right_premise with a resolved literal. *)
    val with_resolved_literal =
      reconstruct_sup
        ctxt
        { left_premise = right_premise
        , literal = (JLit.Left, literal)
        , right_premise = unit
        , subterm = ([], unit_orientation, 0) }
  in
    reconstruct_delete_resolved_lits
      { premise = with_resolved_literal
      , cposs = [HClause.nprems_of with_resolved_literal - 1] }
  end

(* NOTE: Needs to match Jeha.outer_clausify *)
fun reconstruct_simp_outer_claus ctxt { premise: HClause.hthm, literal } =
  let
    (* Each of these replaces the rhs of the `\<Longrightarrow>` by the lhs. *)

    fun neq_true_tac ctxt = resolve_tac ctxt [@{lemma "\<not> A \<Longrightarrow> A \<noteq> True" by auto}]
    fun neq_false_tac ctxt = resolve_tac ctxt [@{lemma "A \<Longrightarrow> A \<noteq> False" by auto}]
    fun lit_to_pred_tac ctxt = FIRST' [neq_true_tac ctxt, neq_false_tac ctxt]

    fun eq_to_lit_tac ctxt = resolve_tac ctxt [@{lemma "s = t \<Longrightarrow> s = t" by auto}]
    fun neq_to_lit_tac ctxt = resolve_tac ctxt [@{lemma "s \<noteq> t \<Longrightarrow> s \<noteq> t" by auto}]
    (* We prefer equalities in literals, so inequalities in negated literals. *)
    fun not_to_eq_false_tac ctxt = resolve_tac ctxt [@{lemma "A \<noteq> True \<Longrightarrow> \<not>A" by auto}]
    fun to_eq_true_tac ctxt = resolve_tac ctxt [@{lemma "A \<noteq> False \<Longrightarrow> A" by auto}]
    fun pred_to_lit_tac ctxt =
      FIRST'
        ([eq_to_lit_tac ctxt, neq_to_lit_tac ctxt] (* equalities stay equalities *)
        @ [not_to_eq_false_tac ctxt, to_eq_true_tac ctxt])

    fun dne_tac ctxt = resolve_tac ctxt [@{lemma "A \<Longrightarrow> \<not>\<not>A" by auto}]

    fun not_and_tac ctxt = resolve_tac ctxt [@{lemma "\<not>A \<or> \<not>B \<Longrightarrow> \<not>(A \<and> B)" by auto}]
    fun not_or_tac ctxt = resolve_tac ctxt [@{lemma "\<not>A \<and> \<not>B \<Longrightarrow> \<not>(A \<or> B)" by auto}]
    (* push negations down *)
    fun demorgan_tac ctxt = FIRST' [not_and_tac ctxt, not_or_tac ctxt]

    fun and_tac ctxt = resolve_tac ctxt @{thms HOL.conjI} (* P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q *)
    
    fun or_tac_1 ctxt = resolve_tac ctxt @{thms HOL.disjI1} (* P \<Longrightarrow> P \<or> Q *)
    fun or_tac_2 ctxt = resolve_tac ctxt @{thms HOL.disjI2} (* Q \<Longrightarrow> P \<or> Q *)
    (* doubles the number of clauses *)
    fun or_tac ctxt = or_tac_1 ctxt APPEND' or_tac_2 ctxt

    fun imp_tac ctxt =
      resolve_tac ctxt [@{lemma "\<not>A \<or> B \<Longrightarrow> A \<longrightarrow> B" by auto}]
      THEN' or_tac ctxt

    fun not_imp_tac ctxt =
      resolve_tac ctxt [@{lemma "A \<Longrightarrow> \<not>B \<Longrightarrow> \<not>(A \<longrightarrow> B)" by auto}]

    fun oc_tac ctxt =
      (* all_tac to ignore equality literals etc. *)
      FIRST' [and_tac ctxt, or_tac ctxt, imp_tac ctxt, not_imp_tac ctxt, K all_tac]

    fun oc_wrapper ctxt tac i th =
      let
        val wrapped_tac =
          lit_to_pred_tac ctxt
          THEN' REPEAT o dne_tac ctxt
          THEN' TRY o demorgan_tac ctxt
          THEN' tac
          (* Some oc cases produce multiple clauses, we want all of them. *)
          THEN_ALL_NEW REPEAT o dne_tac ctxt
          THEN_ALL_NEW pred_to_lit_tac ctxt
      in
        Jeha_Proof_Util.with_all_vars_fixed ctxt (wrapped_tac i) th
        (* wrapped_tac i th *)
        |> Seq.chop 2
        |> (fn (clauses, tail) =>
          case Seq.pull tail of
            SOME _ =>
              (* This can't happen because outer clausification only clausfies one layer of \<or> at a
              time. *)
              error "outer_clausification reconstruction produced more than two clauses"
          | NONE => clauses)
      end

    fun move_new_literals_to_last (conclusion: HClause.hthm) =
      let
        (* Note that one literal has been removed, but we're not counting that. *)
        val number_of_new_literals = HClause.nprems_of conclusion - HClause.nprems_of premise + 1
        (* We move to the left, starting from the left, so the positions shift down by one after
        each move. Thus the position of the literal we're moving next is always the same. *)
        val make_last_cposs = replicate number_of_new_literals literal
      in
        fold HClause.make_last make_last_cposs conclusion
      end
  in
    premise
    |> HClause.traverse_hthm (oc_wrapper ctxt (oc_tac ctxt) (literal + 1))
    |> map move_new_literals_to_last
  end

fun reconstruct_neg_ext ctxt { premise, literal, skolems } =
  let
    val (s, s', false) = HClause.dest_lit_at literal premise
    val [(skolem_const, skolem_with_args, skolem_def)] = skolems
    val lemma =
      (* FIXME: move construction of HClause.hthm into forall_exists_rw_lemma function *)
      { th = Jeha_Lemma.neg_ext_lemma ctxt (s, s') (skolem_const, skolem_with_args, skolem_def)
      , skolems = [(skolem_const, skolem_def)] 
      }
    (*
    val T = s |> Thm.ctyp_of_cterm |> Thm.dest_ctyp0
    val rT = s |> Thm.ctyp_of_cterm |> Thm.dest_ctyp1
    val lemma = \<^instantiate>\<open>s and s' and 'a=T and 'b=rT in
      lemma \<open>
        (s :: 'a \<Rightarrow> 'b) (SOME x_neg_ext. s x_neg_ext \<noteq> s' x_neg_ext)
          = s' (SOME x_neg_ext. s x_neg_ext \<noteq> s' x_neg_ext)
        \<Longrightarrow> s = s'\<close>
      by (insert someI_ex[of "\<lambda>uub. s uub \<noteq> s' uub"], blast)\<close>
    *)
    val conclusion =
      premise
      |> HClause.move_from_to literal 0
      |> HClause.comp_no_flatten_no_incr (lemma, 1) 1
      |> HClause.move_from_to 0 literal
  in
    conclusion
  end
(* Use Thm.instantiate and assume that P is Var (("P", 0), _) *)

(*
(* FIXME: not needed right now *)
fun instantiate_env (Envir.Envir { maxidx, tenv, tyenv }) =
  (* TODO: maxidx *)
  let
    (* Why does tenv store type * term pairs? Why typ? *)
    val tenv_keys_values = Vartab.dest tenv
    val tyenv_keys_values = Vartab.dest tyenv
    (* val tenv = Vartab.map (fn indexname => fn (typ, term) => error "fix") *)
  in
    error "unimplemented"
  end
*)

fun replay_inference ctxt clause_db origin (reconstructed_clause_db : HClause.hthm Inttab.table) =
  let
    fun get_thm id =
      Inttab.lookup reconstructed_clause_db id
      |> (fn x => case x of
            SOME x => HClause.map_hthm (Jeha_Proof_Util.norm_negative_predicate_literals ctxt) x
          | NONE => error
              ("premise " ^ @{make_string} (clause_db id) ^ " missing from reconstructed clauses"))
    fun get_and_instantiate (substitution: Envir.env) (shift: int option) (id: int) =
      get_thm id 
      |> HClause.incr_indexes (the_default 0 shift)
      |> HClause.map_hthm (Jeha_Proof_Util.envir_norm_thm ctxt substitution)
    val conclusion =
      case origin of
        Jeha_Log.Axiom { thm } =>
          thm
          |> hclause_of_axiom ctxt
          |> HClause.map_hthm (Jeha_Proof_Util.envir_norm_thm ctxt Envir.init)
      | Jeha_Log.Sup { left_premise, left_premise_shift, right_premise, literal, subterm, substitution } =>
          reconstruct_sup
            ctxt
            { left_premise = get_and_instantiate substitution (SOME left_premise_shift) left_premise
            , right_premise = get_and_instantiate substitution NONE right_premise
            , literal = literal
            , subterm = subterm }
      (*
      | Jeha_Log.FluidSup =>
          Jeha_Log.FluidSup
      *)
      | Jeha_Log.ERes { premise, literal, substitution } =>
          reconstruct_eres { literal = literal, premise = get_and_instantiate substitution NONE premise }
      | Jeha_Log.EFact { premise, left_literal, right_literal, substitution } =>
          reconstruct_efact
            { left_literal = left_literal
            , right_literal = right_literal
            , premise = get_and_instantiate substitution NONE premise }
      | Jeha_Log.ArgCong { premise, substitution, literal, vars } =>
         reconstruct_arg_cong ctxt { premise = get_and_instantiate substitution NONE premise, literal = literal, vars = vars }
      | Jeha_Log.BoolHoist { premise, subterm, substitution } =>
          reconstruct_bool_hoist
            ctxt
            { premise = get_and_instantiate substitution NONE premise, subterm = subterm }
      | Jeha_Log.FalseElim { premise, literal, substitution } =>
          reconstruct_false_elim
            ctxt
            { premise = get_and_instantiate substitution NONE premise, literal = literal }
      | Jeha_Log.EqHoist { premise, subterm, substitution } =>
          reconstruct_eq_hoist
            ctxt
            { premise = get_and_instantiate substitution NONE premise, subterm = subterm }
      | Jeha_Log.NeqHoist { premise, subterm, substitution } =>
          reconstruct_neq_hoist
           ctxt
           { premise = get_and_instantiate substitution NONE premise, subterm = subterm }
      | Jeha_Log.ForallHoist { premise, subterm, substitution, fresh_x } =>
          let
            val { uninstantiated_premise, predicate, subterm, fresh_x } =
              prepare_forall_exists_hoist_log
                ctxt
                clause_db
                { uninstantiated_premise = premise
                , subterm = subterm
                , substitution = substitution
                , fresh_x = fresh_x }
            (* val premise = only_instantiate substitution uninstantiated_premise *)
            val premise = get_and_instantiate substitution NONE (JClause.id uninstantiated_premise)
          in
            reconstruct_forall_hoist
              ctxt
              { premise = premise, predicate = predicate, subterm = subterm, fresh_x = fresh_x }
          end
      | Jeha_Log.ExistsHoist { premise, subterm, substitution, fresh_x } =>
          let
            val { uninstantiated_premise, predicate, subterm, fresh_x } =
              prepare_forall_exists_hoist_log
                ctxt
                clause_db
                { uninstantiated_premise = premise
                , subterm = subterm
                , substitution = substitution
                , fresh_x = fresh_x }
            (* val premise = only_instantiate substitution uninstantiated_premise *)
            val premise = get_and_instantiate substitution NONE (JClause.id uninstantiated_premise)
          in
            reconstruct_exists_hoist
              ctxt
              { premise = premise, predicate = predicate, subterm = subterm, fresh_x = fresh_x }
          end
      | Jeha_Log.BoolRw { premise, subterm, subrule, substitution } =>
          let
            val instantiated_subrule =
              subrule
              |> Jeha_Lemma.hclause_of_uninstantiated_bool_rw_rule ctxt
              |> Jeha_Proof_Util.envir_norm_thm ctxt substitution
          in
            reconstruct_bool_rw
              ctxt
              { premise = get_and_instantiate substitution NONE premise
              , subterm = subterm
              , instantiated_subrule = HClause.of_lemma instantiated_subrule }
          end
      | Jeha_Log.ForallRw { premise, subterm, substitution, skolems } =>
          let
            val { predicate, subterm, uninstantiated_premise, skolems } =
              prepare_forall_exists_rw_log
                clause_db
                { uninstantiated_premise = premise, subterm = subterm, substitution = substitution, skolems = skolems }
            (* val premise = only_instantiate substitution uninstantiated_premise *)
            val premise = get_and_instantiate substitution NONE (JClause.id uninstantiated_premise)
          in
            reconstruct_forall_rw ctxt { predicate = predicate, subterm = subterm, premise = premise, skolems = skolems }
          end
      | Jeha_Log.ExistsRw { premise, subterm, substitution, skolems } =>
          let
            val { predicate, subterm, uninstantiated_premise, skolems } =
              prepare_forall_exists_rw_log
                clause_db
                { uninstantiated_premise = premise, subterm = subterm, substitution = substitution, skolems = skolems }
            (* val premise = only_instantiate substitution uninstantiated_premise *)
            val premise = get_and_instantiate substitution NONE (JClause.id uninstantiated_premise)
          in
            reconstruct_exists_rw ctxt { predicate = predicate, subterm = subterm, premise = premise, skolems = skolems }
          end
      | Jeha_Log.FluidBoolHoist { premise, subterm, substitution } =>
          error "manual FluidBoolHoist reconstruction unimplemented"
      | Jeha_Log.FluidLoobHoist { premise, subterm, substitution } =>
          error "manual FluidLoobHoist reconstruction unimplemented"
      | Jeha_Log.Ext =>
          error "manual Ext reconstruction unimplemented" 
      | Jeha_Log.Choice =>
          error "manual Choice reconstruction unimplemented" 
      | Jeha_Log.DeleteDuplicatedLits { premise, duplicate_cposs } =>
          reconstruct_delete_duplicated_lits
            { premise = get_thm premise, duplicate_cposs = duplicate_cposs }
      | Jeha_Log.DeleteResolvedLits { premise, cposs } =>
          reconstruct_delete_resolved_lits { premise = get_thm premise, cposs = cposs }
      | Jeha_Log.RewritePositiveLits { unit, unit_shift, unit_orientation, right_premise, subterm, substitution } =>
          reconstruct_sup
            ctxt
            { left_premise = get_and_instantiate substitution (SOME unit_shift) unit
            , right_premise = get_thm right_premise
            , literal = (unit_orientation, 0)
            , subterm = subterm }
      | Jeha_Log.RewriteNegativeLits { unit, unit_shift, unit_orientation, right_premise, subterm, substitution } =>
          reconstruct_sup
            ctxt
            { left_premise = get_and_instantiate substitution (SOME unit_shift) unit
            , right_premise = get_thm right_premise
            , literal = (unit_orientation, 0)
            , subterm = subterm }
      | Jeha_Log.PositiveSimplifyReflect { unit, unit_shift, unit_orientation, matcher, right_premise, disagreement } =>
          reconstruct_positive_simplify_reflect
            ctxt
            { unit = get_and_instantiate matcher (SOME unit_shift) unit
            , unit_orientation = unit_orientation
            , right_premise = get_thm right_premise
            , disagreement = disagreement }
      | Jeha_Log.NegativeSimplifyReflect { unit, matcher, unit_shift, unit_orientation, right_premise, literal } =>
          reconstruct_negative_simplify_reflect
            ctxt
            { unit = get_and_instantiate matcher (SOME unit_shift) unit
            , unit_orientation = unit_orientation
            , right_premise = get_thm right_premise
            , literal = literal }
      | Jeha_Log.SimpPosNegOuterClaus { premise, literal, conclusion_index }  =>
          nth
            (reconstruct_simp_outer_claus ctxt { premise = get_thm premise, literal = literal })
            conclusion_index
      | Jeha_Log.SimpBoolRw { premise, subterm, subrule, substitution } =>
          (* See BoolRw above *)
          let
            val instantiated_subrule =
              subrule
              |> Jeha_Lemma.hclause_of_uninstantiated_bool_rw_rule ctxt
              |> Jeha_Proof_Util.envir_norm_thm ctxt substitution
          in
            reconstruct_bool_rw
              ctxt
              { premise = get_and_instantiate substitution NONE premise
              , subterm = subterm
              , instantiated_subrule = HClause.of_lemma instantiated_subrule }
          end
      | Jeha_Log.SimpFalseElim { premise, literal, substitution } =>
          (* See FalseElim above *)
          reconstruct_false_elim
            ctxt
            { premise = get_and_instantiate substitution NONE premise, literal = literal }
      | Jeha_Log.NegExt { premise, literal, skolems } =>
          reconstruct_neg_ext
            ctxt
            { premise = get_thm premise, literal = literal, skolems = skolems }
      (*
      | Jeha_Log.SyntacticTautologyDeletion1 { premise, literal, substitution } =>
          Jeha_Log.SyntacticTautologyDeletion1 { premise = f premise, literal = literal, substitution = substitution }
      | Jeha_Log.SyntacticTautologyDeletion2 { premise, left_literal, right_literal, substitution } =>
          Jeha_Log.SyntacticTautologyDeletion2 { premise = f premise, left_literal = left_literal, right_literal = right_literal, substitution = substitution }
      | Jeha_Log.ClauseSubsumption { subsumer, subsumed, substitution } =>
          Jeha_Log.ClauseSubsumption { subsumer = subsumer, subsumed = subsumed, substitution = substitution }
      | Jeha_Log.EqualitySubsumption { unit, disagreement, substitution } =>
          Jeha_Log.EqualitySubsumption { unit = f unit, disagreement = disagreement, substitution = substitution }
      | Jeha_Log.Invalid =>
          Jeha_Log.Invalid
*)    
      | origin => error ("replay_inference unimplemented for " ^ @{make_string} origin)
  in
    conclusion
    |> HClause.map_hthm Drule.eta_contraction_rule
    |> HClause.map_hthm (Jeha_Proof_Util.norm_negative_predicate_literals ctxt)
  end

(* Topological sort of a rooted DAG without cycle detection. Note that the parent / children
terminology is swapped compared to that of clauses. *)
fun toposort_acyclic_rooted fuel (lookup_children: int -> int list) (i: int) (visited, sorted) =
  if fuel <= 0 then
    error ("toposort out of fuel: Either the clause graph contains a cycle or my assumption that"
      ^ " the contradiction's clause id would be an appropriate upper bound is wrong")
  else
  if exists (curry (op =) i) visited
    then (visited, sorted)
    else
      let
        (* ensure i will be added to sorted only by us *)
        val visited = i::visited
        val children = lookup_children i
        val (visited, sorted) =
          fold (toposort_acyclic_rooted (fuel - 1) lookup_children) children (visited, sorted)
      in
        (visited, i::sorted)
      end

fun toposort_clauses clause_db contradiction =
  toposort_acyclic_rooted
    (contradiction + 10) (* Use the  id as fuel because the toposort has no cycle detection *)
    (Jeha_Log.premises o JClause.origin o clause_db)
    contradiction
    ([], [])
  |> #2
  |> rev

fun discharge_skolem_prems ctxt ({ th, skolems } : HClause.hthm) : thm =
  let
    (* FIXME: what about TFrees? (hidden polymorphism?) *)
    val skolem_frees_names = map (fst o dest_Free o fst) skolems
    val skolem_frees_names_unsuffixed = map Name.dest_skolem skolem_frees_names
    val (fixed_names, ctxt_fixed) = Variable.add_fixes skolem_frees_names_unsuffixed ctxt
    val () = if fixed_names <> skolem_frees_names then
        (* If this happens, we need to rethink how we declare the fixed names. Pointers:
        Variable.add_fixes_direct, Variable.is_body *)
        error ("discharge_skolem_prems: The fixed names should have been: "
          ^ @{make_string} skolem_frees_names ^ " but were " ^ @{make_string} fixed_names) else ()
    val () = writeln "DEBUG discharge_skolem_prems"
    val () = writeln ("th " ^ @{make_string} th)
    val [th_with_schematic_skolem_prems] = Variable.export ctxt_fixed ctxt [th]
    val () = writeln ("th_with_schematic_skolem_prems " ^ @{make_string} th_with_schematic_skolem_prems)
    val discharged_fixed: thm =
      funpow
        (length skolems)
        (curry (op RS) @{thm "HOL.refl"})
        th_with_schematic_skolem_prems
    val () = writeln ("discharged_fixed " ^ @{make_string} discharged_fixed)
    val [discharged] = Variable.export ctxt ctxt_fixed [discharged_fixed]
    val () = writeln ("discharged " ^ @{make_string} discharged)
  in
    discharged
  end

fun reconstruct_manual
  ctxt
  (clause_db : int -> JClause.T)
  id
  : thm
=
  let
    val clauses =
      toposort_clauses clause_db id
      |> (fn x => (Jeha_Common.trace_msg ctxt (fn () => "RECONSTRUCTION sorted clauses" ^ @{make_string} x); x))
      |> map clause_db
    fun replay_and_insert clause (reconstructed_clause_db : HClause.hthm Inttab.table) =
      let
        val expected_conclusion = HClause.hol_of_clause ctxt false clause
        val () = Jeha_Common.trace_msg ctxt (fn () =>
          "RECONSTRUCTING:\n"
          ^ JClause.pretty_clause ctxt clause
          ^ "\n(origin: " ^ @{make_string} (JClause.origin clause) ^ ")" )
        val replayed: HClause.hthm =
          replay_inference ctxt clause_db (JClause.origin clause) reconstructed_clause_db
        val () =
          if not (expected_conclusion aconvc (HClause.cprop_without_skolem_prems replayed))
            then Jeha_Common.trace_msg ctxt (fn () =>
              "RECONSTRUCTION: WARNING: reconstructed clause " ^ @{make_string} replayed ^ " does not match expected conclusion " ^ @{make_string} expected_conclusion
              (* ^ "\n (compared " ^ Jeha_Common.pretty_term (Jeha_Common.verbose_of ctxt) (Thm.prop_of replayed) ^ " and " ^ Jeha_Common.pretty_term (Jeha_Common.verbose_of ctxt) (Thm.term_of expected_conclusion) ^ ")" *)
              (* ^ "\n (compared " ^ @{make_string} (Thm.prop_of replayed) ^ " and " ^ @{make_string} (Thm.term_of expected_conclusion) ^ ")" *)
              )
            else ()
      in
        Inttab.update_new (JClause.id clause, replayed) reconstructed_clause_db
      end
    val reconstructed_clause_db = fold replay_and_insert clauses Inttab.empty 
  in
    case Inttab.lookup reconstructed_clause_db id of
      SOME reconstructed_contradiction =>
        reconstructed_contradiction
        |> discharge_skolem_prems ctxt
    | NONE => error "contradiction wasn't reconstructed"
  end

fun reconstruct ctxt (clause_db : int -> JClause.T) id =
  case Jeha_Common.get_proof_reconstruction_mode ctxt of
    Jeha_Common.Manual => reconstruct_manual ctxt clause_db id 
  | _ => error "Only Manual reconstruction is implemented."

end;