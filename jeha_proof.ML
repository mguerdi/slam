(* detailed proof and proof reconstruction *)

signature JEHA_PROOF =
sig
  (* type proof_step *)
  (* val hol_thm_of_clause : Proof.context -> (int -> JClause.T) -> int -> thm *)
  (* elaborates a \<lambda>oSup inference into a series of more smaller proof steps *)
  (* val fun proof_steps_of_inference : Jeha_Log.inference -> proof_step *)
  
  val reconstruct_with_metis : Proof.context -> (int -> JClause.T) -> int -> thm
  val instantiate : Proof.context -> Type.tyenv * Envir.tenv -> thm -> thm

  val fix_vars : Proof.context -> thm list -> cterm -> Proof.context * thm list * cterm

  (* for testing and debugging *) 
  val get_lemmas:
    Proof.context -> (int -> JClause.T) -> thm Inttab.table -> Jeha_Log.inference -> cterm -> int
    -> thm list 
  val get_instantiated_premises:
    Proof.context -> (int -> JClause.T) -> thm Inttab.table -> Jeha_Log.inference
    -> thm Inttab.table * thm list
  val resolve_against_arg_cong_contrapositive_n_times : Proof.context -> int -> thm * int -> thm
  (* The records are modelled after those in Jeha_Log, but with int replace by HClause.htm *)
  val reconstruct_arg_cong : Proof.context -> int -> thm * int -> cterm -> thm 
  val reconstruct_sup:
    Proof.context
    -> { left_premise: HClause.hthm
       , literal: JLit.lpos * JClause.cpos
       , right_premise: thm
       , subterm: JClause.full_pos }
    -> HClause.hthm
  val reconstruct_delete_duplicated_lits:
    { premise: HClause.hthm
    , duplicate_cposs: { duplicate: JClause.cpos, duplicate_of: JClause.cpos } list }
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
end;

structure Jeha_Proof : JEHA_PROOF =
struct

(* FIXME: see also Pure/ML/ml_instantiate.ML *)
fun instantiate_norm ctxt (tyenv, tenv) thm =
  (* see metis_reconstruct.ML, flexflex_first_order *)
  let
    val _ = Jeha_Common.trace_msg ctxt (fn () =>
      "instantiating (norm)\n\t" ^
      Thm.string_of_thm ctxt thm ^
      "\nwith substitution\n\t" ^
      Jeha_Common.pretty_tenv ctxt (tenv) ^
      "\n\t" ^
      Jeha_Common.pretty_tyenv ctxt (tyenv))

    (* FIXME: more chasing? look at thm.ML prep_insts, etc. *)
    fun mkT (v, (S, T)) = ((v, S), Thm.ctyp_of ctxt T)
    (* FIXME: there is no norm_term_types... *)
    fun mk (v, (T, t)) = ((v, Envir.norm_type tyenv T), Thm.cterm_of ctxt (Envir.subst_term_types tyenv t))

    val instsT = Vartab.fold (cons o mkT) tyenv []
    val insts = Vartab.fold (cons o mk) tenv []
  in
    Thm.instantiate (TVars.make instsT, Vars.make insts) thm
  end
  
fun instantiate_norm_with_env ctxt env = instantiate_norm ctxt (Envir.type_env env, Envir.term_env env)

fun instantiate ctxt (tyenv, tenv) thm =
  (* see metis_reconstruct.ML, flexflex_first_order *)
  let
    val _ = Jeha_Common.trace_msg ctxt (fn () =>
      "instantiating\n\t" ^
      Thm.string_of_thm ctxt thm ^
      "\nwith substitution\n\t" ^
      Jeha_Common.pretty_tenv ctxt (tenv) ^
      "\n\t" ^
      Jeha_Common.pretty_tyenv ctxt (tyenv))

    fun mkT (v, (S, T)) = ((v, S), Thm.ctyp_of ctxt T)
    fun mk (v, (T, t)) = ((v, Envir.subst_type tyenv T), Thm.cterm_of ctxt t)

    val instsT = Vartab.fold (cons o mkT) tyenv []
    val insts = Vartab.fold (cons o mk) tenv []
  in
    Thm.instantiate (TVars.make instsT, Vars.make insts) thm
  end

fun instantiate_with_env ctxt env = instantiate ctxt (Envir.type_env env, Envir.term_env env)

val excluded_middle =  @{lemma "P \<Longrightarrow> \<not> P \<Longrightarrow> False" by (rule notE)}

fun resolve_against_arg_cong_contrapositive_n_times debug_ctxt number_of_vars (premise_proved, cpos) =
  let
    val () = Jeha_Common.trace_msg debug_ctxt (fn () => "RS_ARG_CONG premise_proved: " ^ Thm.string_of_thm debug_ctxt premise_proved)
  in
    if number_of_vars < 0 then
      error "can't do something a negative number of times"
    else
      funpow number_of_vars (fn th =>
        let
          val () = Jeha_Common.trace_msg debug_ctxt (fn () => "RS_ARG_CONG current (cpos=" ^ @{make_string} cpos ^"): " ^ Thm.string_of_thm debug_ctxt th)
        in
          @{thm arg_cong_contrapositive} RSN (cpos + 1, th)
        end
      ) premise_proved
  end

fun reconstruct_arg_cong ctxt number_of_vars (premise, cpos) goal =
  let
    val goal_proved_but_with_schematic_vars =
      resolve_against_arg_cong_contrapositive_n_times ctxt number_of_vars (premise, cpos)
  in
      goal
      |> Goal.init
      |> ((* print_tac ctxt "A"
        THEN *) resolve_tac ctxt [goal_proved_but_with_schematic_vars] 1
        (* THEN print_tac ctxt "B" *)
        (* assume_tac is needed one or two times (in the examples I've seen so far) *)
        THEN ALLGOALS (assume_tac ctxt)
        (* THEN print_tac ctxt "D" *))
      |> Seq.hd
      |> Goal.finish ctxt
  end
  

(* \<not> is to be viewed as a metafunction, i.e. \<not>D' is not a proper term but a list of assumptions:

\<not>D' \<Longrightarrow> t /\<approx> t' \<Longrightarrow> False   \<not>C\<langle>t\<rangle>\<^sub>p \<Longrightarrow> False
-------------------------------------------- GroundSup
         \<not>D' \<Longrightarrow> \<not>C\<langle>t'\<rangle>\<^sub>p \<Longrightarrow> False
*)
fun reconstruct_sup
  ctxt
  { left_premise
  , right_premise
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
      |> HClause.orient_positive_consequent_lit literal_orientation
    val (ct, ct') =
      notD'_imp_t_eq_t'
      |> Thm.concl_of
      |> HOLogic.dest_Trueprop
      |> HOLogic.dest_eq
      |> apply2 (Thm.cterm_of ctxt)
    val cT = Thm.ctyp_of_cterm ct
    (* x \<mapsto> (\<not>C\<langle>x\<rangle>\<^sub>p \<Longrightarrow> False) *)
    val C_abs =
      HClause.abstract_over_green_subterm
        subterm_position
        (Thm.prop_of right_premise)
        (* We could do without this if we could assume that all schematic variables are fixed
        because this variable is short lived anyways. *)
        (Thm.maxidx_of right_premise)
      |> Thm.cterm_of ctxt
    val C_congruence_wrt_subterm_position =
      (* Without PROP the parser refuses to read f as having return type prop (instead of bool). *)
      \<^instantiate>\<open>x=ct and y=ct' and f=C_abs and 'a=cT in
        lemma \<open>(x :: 'a) = y \<Longrightarrow> PROP f x \<Longrightarrow> PROP f y\<close> by auto\<close>
    (* \<not>D' \<Longrightarrow> (\<not>C t \<Longrightarrow> False) \<Longrightarrow> (\<not>C t' \<Longrightarrow> False) *)
    val notD'_imp_Ct_imp_Ct' = notD'_imp_t_eq_t' RS C_congruence_wrt_subterm_position
    val Ct_cpos = Logic.count_prems (Thm.prop_of left_premise) (* number of literals of D *)
    (* compose (\<not>C t \<Longrightarrow> False) and (\<not>D' \<Longrightarrow> (\<not>C t \<Longrightarrow> False) \<Longrightarrow> (\<not>C t' \<Longrightarrow> False))
    obtaining \<not>D' \<Longrightarrow> (\<not>C t' \<Longrightarrow> False) *)
    val notD'_imp_Ct' = Drule.compose (right_premise, Ct_cpos, notD'_imp_Ct_imp_Ct')
  in
    (* This is an HClause.T if right_premise is an HClause.T. *)
    notD'_imp_Ct' 
  end

(*
\<not>C' \<Longrightarrow> u=u \<Longrightarrow> False
--------------------- ERes
    \<not>C' \<Longrightarrow> False
*)
fun reconstruct_eres {premise, literal} =
  let
    val (u, _, false) = HClause.dest_lit_at literal premise 
    val uT = Thm.ctyp_of_cterm u
  in
    Drule.compose
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
      (Thm.cprem_of premise (snd right_literal + 1))
      |> Thm.dest_arg (* dest_Trueprop *)
      |> Thm.dest_arg (* strip negation *)
      |> Drule.strip_comb
    val (_, [_, v']) =
      (Thm.cprem_of premise (snd left_literal + 1))
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
    val length_of_C' = Thm.nprems_of premise - 2
    val uT = Thm.ctyp_of_cterm u
    val lemma = \<^instantiate>\<open>u=u and v=v and v'=v' and 'a = uT in
      lemma \<open>((u :: 'a) \<noteq> v' \<Longrightarrow> u \<noteq> v \<Longrightarrow> False) \<Longrightarrow> v = v' \<Longrightarrow> u \<noteq> v' \<Longrightarrow> False\<close>
      by auto\<close>
    val D = Drule.comp_no_flatten (C, length_of_C') 1 lemma
    (* Rotate back, compare JClause.add_literal. Note: cpos, i.e. 0-based *)
    val conclusion =
      D
      |> HClause.move_last_to 0
      |> HClause.move_last_to 1
  in
    conclusion
  end

fun reconstruct_false_elim ctxt { premise, literal } =
  (* \<not>C' \<Longrightarrow> \<bottom> /\<approx> \<top> \<Longrightarrow> False *)
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
    Drule.comp_no_flatten (C, Thm.nprems_of C) 1 @{lemma \<open>False = True \<Longrightarrow> False\<close> by auto}
  end

fun impl_delete_duplicated_lit {duplicate, duplicate_of} premise =
  let
    val () = \<^assert> (duplicate_of < duplicate)
  in
    premise
    |> HClause.make_last duplicate_of
    |> HClause.make_last duplicate 
    |> HClause.merge_duplicated_lit_last
    |> HClause.move_last_to duplicate_of
  end

fun reconstruct_bool_hoist ctxt { premise, subterm = subterm_position } =
  let
    val subterm =
      HClause.green_subterm_at_full_pos (Thm.prop_of premise) subterm_position
      |> Thm.cterm_of ctxt 
    val lemma = \<^instantiate>\<open>x=subterm in lemma \<open>x \<noteq> True \<Longrightarrow> x \<noteq> False \<Longrightarrow> False\<close> by auto\<close>
    val conclusion_from_sup =
      reconstruct_sup
        ctxt
        { left_premise = lemma
        , literal = (JLit.Left, 1)
        , right_premise = premise
        , subterm = subterm_position }
  in
    HClause.make_last 0 conclusion_from_sup 
  end
  
(* fun reconstruct_delete_duplicated_lits { premise = premise, literal, duplicate } = *)
fun reconstruct_delete_duplicated_lits { premise, duplicate_cposs } =
  let
    (* jeha.ML already guarantees this, just to be safe *)
    val sorted = sort (rev_order o int_ord o apply2 #duplicate) duplicate_cposs
  in
    fold impl_delete_duplicated_lit sorted premise
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

fun impl_forall_exists_hoist_lemma
  ctxt
  clause_db
  is_forall_hoist
  {premise = premise, subterm = subterm, substitution = substitution, fresh_x = fresh_x}
=
  let
    (* Only the instantiation of the type is strictly necessary, as the fresh variable will remain
    unchanged in the conclusion (except for its type). *)
    val x = JTerm.norm_beta_eta_qeta_env substitution fresh_x
    val cx = Thm.cterm_of ctxt x
    val T = Thm.ctyp_of ctxt (fastype_of x)
    
    val premise = clause_db premise
    val (quantifier $ predicate_variable) = JClause.subterm_at_full_pos premise subterm
    val () = \<^assert> (JTerm.is_quantifier quantifier)
    val predicate = JTerm.norm_beta_eta_qeta_env substitution predicate_variable
    val P = Thm.cterm_of ctxt predicate
    (* val _ = Jeha_Common.trace_msg ctxt (fn () => "forall_rw_lemma: P = " ^ Jeha_Common.pretty_term ctxt predicate)
    val _ = Jeha_Common.trace_msg ctxt (fn () => "forall_rw_lemma: typ_of_x = " ^ Jeha_Common.pretty_typ ctxt (fastype_of fresh_x)) *)
  in
    if is_forall_hoist then
      (* [Thm.instantiate'
        [SOME typ_of_x]
        [SOME P, SOME cx]
        @{lemma \<open>P (x :: 'b) = False \<Longrightarrow> (\<forall>x. P x) = True \<Longrightarrow> False\<close> by auto}] *)
      [\<^instantiate>\<open>
          'T=T and P and cx in
          lemma (open) \<open>P (cx :: 'T) = False \<Longrightarrow> (\<forall>x. P x) = True \<Longrightarrow> False\<close> by auto\<close>]
    else
      [\<^instantiate>\<open>
          'T=T and P and cx in
          lemma (open) \<open>P (cx :: 'T) = True \<Longrightarrow> (\<exists>x. P x) = False \<Longrightarrow> False\<close> by auto\<close>]
  end

fun forall_hoist_lemma ctxt clause_db (Jeha_Log.ForallHoist args) =
  impl_forall_exists_hoist_lemma ctxt clause_db true args

fun exists_hoist_lemma ctxt clause_db (Jeha_Log.ExistsHoist args) =
  impl_forall_exists_hoist_lemma ctxt clause_db false args
    
(* Use Thm.instantiate and assume that P is Var (("P", 0), _) *)

(* some inference rules require additional lemmas *)
(* All variables occuring the lemma, which don't come from the substitution must be greater than
maxidx. *)
fun get_lemmas _ _ _ (Jeha_Log.EqHoist _) _ maxidx = [Thm.incr_indexes (maxidx + 1) excluded_middle]
  | get_lemmas _ _ _ (Jeha_Log.NeqHoist _) _ maxidx = [Thm.incr_indexes (maxidx + 1) excluded_middle]
  | get_lemmas ctxt clause_db _ (origin as (Jeha_Log.ForallHoist _)) _ _ =
      forall_hoist_lemma ctxt clause_db origin
  | get_lemmas ctxt clause_db _ (origin as (Jeha_Log.ExistsHoist _)) _ _ =
      exists_hoist_lemma ctxt clause_db origin
  (* need to instantiate verit_sko_forall, and use auto to reconstruct instead of metis *)
  | get_lemmas
      ctxt
      clause_db
      _
      (Jeha_Log.ForallRw {premise = premise, subterm = subterm, substitution = substitution})
      (* todo: use these two *)
      _
      maxidx
    =
      let
        val clause = clause_db premise
        val (quantifier $ predicate_variable) = JClause.subterm_at_full_pos clause subterm
        val () = \<^assert> (JTerm.is_quantifier quantifier)
        val predicate = JTerm.norm_beta_eta_qeta_env substitution predicate_variable
      in
        [forall_rw_lemma ctxt predicate]
      end
  (* | get_lemmas _ _ (Jeha_Log.ArgCong { number_of_vars = number_of_vars, ... }) =
      [resolve_against_arg_cong_contrapositive_n_times
        (number_of_vars - 1)
        @{thm arg_cong_contrapositive}] *)
  | get_lemmas
      ctxt
      _
      reconstructed_clause_db
      (Jeha_Log.ArgCong { premise = premise, literal = literal, number_of_vars = number_of_vars })
      conclusion
      _
    =
      let
        val premise = the (Inttab.lookup reconstructed_clause_db premise) handle Option.Option =>
          error "get_lemmas ArgCong: premise not in reconstructed clause db"
      in
        (* This is not really a lemma but rather the full goal. *)
        [reconstruct_arg_cong ctxt number_of_vars (premise, literal) conclusion]
      end
  | get_lemmas _ _ _ (Jeha_Log.Sup _) _ _ = []
  | get_lemmas _ _ _ _ _ maxidx = [Thm.incr_indexes (maxidx + 1) excluded_middle]

(* fun forall_rw_lemma P = @{thm "verit_sko_forall"[of P]} *)
(*  \<^instantiate>\<open>P in lemma (open) \<open>(\<forall>x. P x) \<longleftrightarrow> P (SOME x. \<not>P x)\<close> by (rule notE)\<close> *)


fun fix_vars ctxt instantiated_premises_thms conclusion_prop =
  let
    (* val vars = 
      []
      |> fold (Term.add_vars o Thm.prop_of) instantiated_premises_thms
      |> Term.add_vars (Thm.term_of conclusion_prop)
    val (fixed_var_names, ctxt_with_fixed_vars) = Variable.add_fixes (map (#1 o #1) vars) ctxt
    val () = \<^assert> (length fixed_var_names = length vars)
    val  *)
  in
    error ""
  end

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



(* This just threads the reconstructed_clause_db cache through get_instantiated_premises but doesn't
directly modify it. *)
fun impl_reconstruct_with_metis
  ctxt
  (clause_db : int -> JClause.T)
  (reconstructed_clause_db: thm Inttab.table)
  id
=
  let
    val clause =
      clause_db id
    val conclusion = HClause.hol_of_clause ctxt false clause

    val origin = JClause.origin (clause_db id)
    
    (* recursive calls *)
    val (new_reconstructed_clause_db, instantiated_premises) = get_instantiated_premises ctxt clause_db reconstructed_clause_db origin
    
    val maxidx = fold Thm.maxidx_thm instantiated_premises (JClause.maxidx clause)
    
    (* only start logging after the recursive calls to avoid nesting *)
    val _ = Jeha_Common.trace_msg ctxt (fn () => "START PROOF")
    val _ = Jeha_Common.trace_msg ctxt (fn () => "clause: " ^ JClause.pretty_clause ctxt (clause_db id))
    val _ = Jeha_Common.trace_msg ctxt (fn () => "origin: " ^ (* @{make_string} *) Jeha_Log.pretty ctxt (JClause.origin (clause_db id)))

    val _ = Jeha_Common.trace_msg ctxt (fn () => "Instantiated Premises: " ^ space_implode "\n" (map (Thm.string_of_thm ctxt) instantiated_premises))
    
    val lemmas = get_lemmas ctxt clause_db new_reconstructed_clause_db origin conclusion maxidx
    
    val _ = Jeha_Common.trace_msg ctxt (fn () => "Lemmas:" ^ space_implode "\n" (map (Thm.string_of_thm ctxt) lemmas))

    val _ = Jeha_Common.trace_msg ctxt (fn () => "Proving: " ^ (Jeha_Common.pretty_term ctxt (Thm.term_of conclusion)))

    val goal = Goal.init conclusion
    
    val _ = Jeha_Common.trace_msg ctxt (fn () => "Goal: " ^ Thm.string_of_thm ctxt goal)

    (* Idea: fix only those variables occuring in the premises. Fix those variables in the lemma.
    Name apart the remaining variables in the lemma (probably not necessary). Fix the variables in
    the lemma (this operation might take care of renaming). *)
    val ((tables, goal_fixed::instantiated_premises_fixed), ctxt_fixed) =
      Variable.import false (goal::instantiated_premises) ctxt

    (* Use tables to replace variables in the lemma by fixed variants of the premise variables. *)
    (* This works because the all variables occuring in the lemmas that are not from the
    substitution, have index greater than the maxidx of the premises and the conclusion *)
    val lemmas_fixed = map (Thm.instantiate tables) lemmas
    
    (* Idea: fix variables in the substitution before instantiating the lemma. Then name apart the lemma. *)
    (* How: Envir.env consists of two Vartab's which have map functions that we can use to replace
    the original terms by their fixed variants. *)
    (* Problem: we don't have the substiution anymore :( *)

    val _ = Jeha_Common.trace_msg ctxt_fixed (fn () => "Fixed Instantiated Premises: " ^ space_implode "\n" (map (Thm.string_of_thm ctxt) instantiated_premises_fixed))
    val _ = Jeha_Common.trace_msg ctxt_fixed (fn () => "Fixed Lemmas: " ^ space_implode "\n" (map (Thm.string_of_thm ctxt) lemmas_fixed))
    val _ = Jeha_Common.trace_msg ctxt_fixed (fn () => "Proving Fixed Goal: " ^ Thm.string_of_thm ctxt goal_fixed)
    
    val final_goal_fixed =
      case Jeha_Common.get_proof_reconstruction_mode ctxt of
        Jeha_Common.Metis =>
        (* from metis_tactic.ML *)
        let
          val method = METHOD oo Metis_Tactic.metis_method
          (* The proof context returned by METHOD is the same as the context that was passed in, see
          TACTIC_CONTEXT in Pure/context_tactic.ML.
          Using the tactic directly (i.e. not as a method) would not yield a new context, but this doesn't
          work, despite leading to (almost?) the same metis trace (iirc). *)
          val SOME (Seq.Result (_, final_goal_fixed), _) =
            method
              ((NONE, NONE (* SOME "opaque_lifting" *)), instantiated_premises_fixed @ lemmas_fixed)
              ctxt
              instantiated_premises_fixed
              (ctxt_fixed, goal_fixed)
            |> Seq.pull
        in 
          final_goal_fixed
        end
      | Jeha_Common.Argo =>
        let
          val SOME (final_goal_fixed, _) = goal_fixed |> (
            (* Use insert_tac instead of passing to argo directly to make repair of undeclared hyps
            work. *)
            Method.insert_tac ctxt_fixed (instantiated_premises_fixed @ lemmas_fixed) 1
            (* Argo proof reconstruction fails even on simple goals involving meta-implication. This
            solves some of the undeclared hyps issues but breaks the fix for eta-contracted
            undeclared hyps below because that relies on meta-hypotheses which aren't available to
            Subgoal.FOCUS after atomization. *)
            (* THEN PRIMITIVE (Conv.gconv_rule (Object_Logic.atomize ctxt_fixed) 1) *)
            (* Fixes eta-contracted undeclared hyps *) 
            THEN Jeha_Argo.repaired_argo_tac ctxt_fixed [] 1
            )
            |> Seq.pull
        in
          final_goal_fixed
        end
      | Jeha_Common.Blast =>
        let
          val SOME (final_goal_fixed, _) = goal_fixed |> blast_tac ctxt_fixed 1 |> Seq.pull
        in
          final_goal_fixed
        end
      | Jeha_Common.Manual => error "Manual proof should happen at an earlier point"
      | Jeha_Common.None => error "We're in proof reconstruction even though it has beeen disabled."

    val proved_conclusion_fixed = Goal.finish ctxt final_goal_fixed

    val [proved_conclusion] = Variable.export ctxt_fixed ctxt [proved_conclusion_fixed]

    val _ = Jeha_Common.trace_msg ctxt (fn () =>
      "Proved conclusion (new vars): " ^ Thm.string_of_thm ctxt proved_conclusion)

    val old_vars = Term.add_vars (Thm.term_of conclusion) []
    val new_vars = Term.add_vars (Thm.prop_of proved_conclusion) []
    val () = \<^assert> (length old_vars = length new_vars)
    (* Doesn't work with Unify.matchers *)
    val new_to_old_matcher =
      fold (Pattern.first_order_match (Proof_Context.theory_of ctxt)) (ListPair.zip (map Var new_vars, map Var old_vars)) (Vartab.empty, Vartab.empty)

    val _ = Jeha_Common.trace_msg ctxt (fn () =>
    "instantiating proved conclusion\n\t" ^
    Thm.string_of_thm ctxt proved_conclusion ^
    "\nwith substitution\n\t" ^
    Jeha_Common.pretty_tenv ctxt (#2 new_to_old_matcher) ^
    "\n\t" ^
    Jeha_Common.pretty_tyenv ctxt (#1 new_to_old_matcher))

    val proved_conclusion_with_old_vars = instantiate ctxt new_to_old_matcher proved_conclusion
    
    val _ = Jeha_Common.trace_msg ctxt (fn () =>
      "Proved conclusion (old vars): " ^  Thm.string_of_thm ctxt proved_conclusion_with_old_vars)

    (* sanity check *)
    val () = if not (Thm.prop_of proved_conclusion_with_old_vars aconv Thm.term_of conclusion)
      then error ("not aconv:\n"
        ^ @{make_string} (Thm.prop_of proved_conclusion_with_old_vars)
        ^ "\nand\n"
        ^ @{make_string} (Thm.term_of conclusion))
      else ()
  in
    (new_reconstructed_clause_db, proved_conclusion_with_old_vars)
  end

(*
FIXME: some lemmas need to be instantiated and fixed others don't
Q: Do I need to partially instantiate any lemmas?
A: probably
Q: To what extend do we have to do renaming of Var's and TVar's in the lemma, w.r.t. the
    instantiated premises
A: Need to rename all variables that are not part of the instantiation (i.e. that come from the
    substitution and are thus part of the premises' shared namespace)
*)
(* Idea:
introduce a concept of namespace: everything between minindex and maxidx is a namespace. This allows
us to differentiate between the lemma's variables and the variables from the substitution *)
(* Plan
1. get uninstantiated premises and substitution
2. instantiate premises
Option 1
3. fix premises (FIXME: can this destroy any subterms that we need for our lemmas (e.g. by
    \<beta>-reduction)? And if yes, isn't this precisely what we want? Because we need the same subterm
    in our lemma as in our fixed clause, at least if we're using a prover that doesn't reason about
    \<lambda>s)
4. instantiate lemma using subterms from fixed clauses 
5. name apart instantiated lemma
6. fix remaining variables in lemma
Option 2
3. Name apart lemma
4. Use Thm.instantiate' to instantiate lemma (without having to know the variable's names) (IDEA: define instantiate helpers in the jeha_lemmas.thy file inside of ML... blocks?)
5. fix premises and lemmas
*)

(* This function manipulates the reconstructed_clause_db cache. *)
(* FIXME: Insert axioms into cache? But they dont have an ID at this point... (or ever?) Or are they being inserted on the recursive calls one level up? *)
and get_instantiated_premises _ _ reconstructed_clause_db (Jeha_Log.Axiom { thm = thm })
      = (reconstructed_clause_db, [thm])
  | get_instantiated_premises ctxt clause_db reconstructed_clause_db origin =
      let
        val ids_and_shifts_and_substituitons = Jeha_Log.premises_shift_substitution origin
        (* recursive calls *)
        val (
          premises_and_shifts_and_substitutions:
            { premise: thm, shift: int, substitution: Envir.env } list,
          new_reconstructed_clause_db
          )
          = fold_map
              (fn { id, shift, substitution } => fn old_reconstructed_clause_db =>
                case Inttab.lookup old_reconstructed_clause_db id of
                  SOME premise => ({ premise = premise, shift = shift, substitution = substitution }, old_reconstructed_clause_db)
                | NONE =>
                    let
                      val (new_reconstructed_clause_db, premise) = impl_reconstruct_with_metis ctxt clause_db old_reconstructed_clause_db id
                    in
                      (
                        { premise = premise,
                          shift = shift,
                          substitution = substitution
                        },
                        (* insert into cache *)
                        Inttab.default (id, premise) new_reconstructed_clause_db 
                      )
                    end
              )
            ids_and_shifts_and_substituitons
            reconstructed_clause_db

        (* FIXME: Move this to the top level of the file, it's only here for a cleaner diff. *)
        fun instantiate_premises ctxt premises_and_shifts_and_substituitons =
          premises_and_shifts_and_substituitons
          |> map (fn { premise = premise, shift, substitution } =>
              premise
              |> Thm.incr_indexes shift
              |> (fn premise =>
                let
                  (* val _ = Jeha_Common.trace_msg ctxt (fn () =>
                    "instantiating premise\n\t" ^
                    Jeha_Common.pretty_term ctxt (Thm.prop_of premise) ^
                    "\nwith substitution\n\t" ^
                    Jeha_Common.pretty_tenv ctxt (Envir.term_env substitution) ^
                    "\n\t" ^
                    Jeha_Common.pretty_tyenv ctxt (Envir.type_env substitution))
                  val var_sub = tenv_to_Vars ctxt (Envir.term_env substitution)
                  val tvar_sub = tyenv_to_TVars ctxt (Envir.type_env substitution) *)
                in
                  (* Thm.instantiate (tvar_sub, var_sub) premise *)
                  instantiate_norm_with_env ctxt substitution premise
                end)
             )

        val instantiated_premises = instantiate_premises ctxt premises_and_shifts_and_substitutions
      in
        (new_reconstructed_clause_db, instantiated_premises)
      end

fun reconstruct_with_metis ctxt (clause_db : int -> JClause.T) id =
  #2 (impl_reconstruct_with_metis ctxt clause_db Inttab.empty id)

end;