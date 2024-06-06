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
end;

structure Jeha_Proof : JEHA_PROOF = 
struct

(* The primitve building blocks to which all o\<lambda>Sup inferences can be reduced. *)
(* datatype proof_step =
    (* FIXME: does normalization need to be separate? *)
    Instantiation of { premise: int, substitution: Envir.env }
  | Sup of { left_premise: int, right_premise: int, literal: JLit.lpos * JClause_Pos.cpos, subterm: JClause_Pos.full_pos }
  | ERes of { premise: int, literal: JClause_Pos.cpos }
  | EFact of { premise: int, left_literal: JLit.lpos * JClause_Pos.cpos, right_literal: JLit.lpos * JClause_Pos.cpos }
  (* FIXME: can this be meaningfully viewed as a kind of superposition? *)
  | ArgCong 
  |

fun proof_steps_of_inference *)

(* turn jeha clause [A, B, C] into formula \<not>A \<Longrightarrow> \<not>B \<Longrightarrow> \<not>C \<Longrightarrow> False *)
fun hol_of_clause ctxt close c =
  let
    val negated_literals = 
      JClause.literals c
      |> map (fn (s, t, b) => (s, t, not b))
      |> map JLit.term_of
      |> map HOLogic.mk_Trueprop
    (* FIXME: remove *)
    val vars =
      fold Term.add_vars negated_literals []
      (* reuse variable names for binder names *)
      |> map (fn idxname_typ => (fst (fst idxname_typ), Var idxname_typ))
  in
    if close
      (* FIXME: remove this `if` and the `close` parameter *)
      then
        Logic.close_prop vars negated_literals @{prop "False"}
        |> Thm.cterm_of ctxt
      else
        Logic.list_implies (negated_literals, @{prop "False"})
        |> Thm.cterm_of ctxt
  end

(* with index 2 turn \<not>A \<Longrightarrow> \<not>B \<Longrightarrow> \<not>C \<Longrightarrow> False into \<not>A \<Longrightarrow> \<not>C \<Longrightarrow> B *)
(* fun move_literal_to_conclusion literal_index *)

fun instantiate_norm ctxt (tyenv, tenv) thm =
  (* see metis_reconstruct.ML, flexflex_first_order *)
  let
    val _ = Jeha_Common.trace_msg ctxt (fn () =>
      "instantiating (norm)\n\t" ^
      Jeha_Common.pretty_term ctxt (Thm.prop_of thm) ^
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
      Jeha_Common.pretty_term ctxt (Thm.prop_of thm) ^
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

(* some inference rules require additional lemmas *)
fun get_lemmas (Jeha_Log.EqHoist _) = [excluded_middle]
  | get_lemmas (Jeha_Log.NeqHoist _) = [excluded_middle]
  | get_lemmas (Jeha_Log.ForallRw _) = [@{thm "verit_sko_forall"}]
  | get_lemmas _ = [excluded_middle]

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

fun impl_reconstruct_with_metis ctxt (clause_db : int -> JClause.T) id =
  let
    val clause =
      clause_db id
    val conclusion = hol_of_clause ctxt false clause

    val (instantiated_premises, lemmas) =
      id
      |> clause_db
      |> JClause.origin
      (* recursive calls *)
      |> get_prems_and_lemmas ctxt clause_db

    (* only start logging here to avoid nesting *)
    val _ = Jeha_Common.trace_msg ctxt (fn () => "START PROOF")
    val _ = Jeha_Common.trace_msg ctxt (fn () => "clause: " ^ JClause.pretty_clause ctxt (clause_db id))
    val _ = Jeha_Common.trace_msg ctxt (fn () => "origin: " ^ @{make_string} (JClause.origin (clause_db id)))

    val _ = Jeha_Common.trace_msg ctxt (fn () => "Instantiated Premises: " ^ (Jeha_Common.pretty_terms ctxt (map Thm.prop_of instantiated_premises)))
    val _ = Jeha_Common.trace_msg ctxt (fn () => "Proving: " ^ (Jeha_Common.pretty_term ctxt (Thm.term_of conclusion)))

    val goal = Goal.init conclusion
    
    val _ = Jeha_Common.trace_msg ctxt (fn () => "Goal: " ^ (Jeha_Common.pretty_term ctxt (Thm.prop_of goal)))
    
    val ((tables, goal_fixed::instantiated_premises_fixed), ctxt_fixed) =
      Variable.import false (goal::instantiated_premises) ctxt

    val _ = Jeha_Common.trace_msg ctxt_fixed (fn () => "Fixed Instantiated Premises: " ^ (Jeha_Common.pretty_terms ctxt (map Thm.prop_of instantiated_premises_fixed)))
    val _ = Jeha_Common.trace_msg ctxt_fixed (fn () => "Proving Fixed Goal: " ^ (Jeha_Common.pretty_term ctxt (Thm.prop_of goal_fixed)))

    (* from metis_tactic.ML *)
    val method = METHOD oo Metis_Tactic.metis_method
    (* The proof context returned by METHOD is the same as the context that was passed in, see
    TACTIC_CONTEXT in Pure/context_tactic.ML.
    Using the tactic directly (i.e. not as a method) would not yield a new context, but this doesn't
    work, despite leading to (almost?) the same metis trace (iirc). *)
    val SOME (Seq.Result (_, final_goal_fixed), _) =
      method
        ((NONE, NONE (* SOME "opaque_lifting" *)), instantiated_premises_fixed @ lemmas)
        ctxt
        instantiated_premises_fixed
        (ctxt_fixed, goal_fixed)
      |> Seq.pull

    val proved_conclusion_fixed = Goal.finish ctxt final_goal_fixed

    val [proved_conclusion] = Variable.export ctxt_fixed ctxt [proved_conclusion_fixed]

    val _ = Jeha_Common.trace_msg ctxt (fn () =>
      "Proved conclusion (new vars): " ^ (Jeha_Common.pretty_term ctxt (Thm.prop_of proved_conclusion)))

    val old_vars = Term.add_vars (Thm.term_of conclusion) []
    val new_vars = Term.add_vars (Thm.prop_of proved_conclusion) []
    val () = \<^assert> (length old_vars = length new_vars)
    (* Doesn't work with Unify.matchers *)
    val new_to_old_matcher =
      fold (Pattern.first_order_match (Proof_Context.theory_of ctxt)) (ListPair.zip (map Var new_vars, map Var old_vars)) (Vartab.empty, Vartab.empty)
    
    val _ = Jeha_Common.trace_msg ctxt (fn () =>
    "instantiating proved conclusion\n\t" ^
    Jeha_Common.pretty_term ctxt (Thm.prop_of proved_conclusion) ^
    "\nwith substitution\n\t" ^
    Jeha_Common.pretty_tenv ctxt (#2 new_to_old_matcher) ^
    "\n\t" ^
    Jeha_Common.pretty_tyenv ctxt (#1 new_to_old_matcher))

    val proved_conclusion_with_old_vars = instantiate ctxt new_to_old_matcher proved_conclusion
    
    val _ = Jeha_Common.trace_msg ctxt (fn () =>
      "Proved conclusion (old vars): " ^ (Jeha_Common.pretty_term ctxt (Thm.prop_of proved_conclusion_with_old_vars)))

    (* sanity check *)
    val () = if not (Thm.prop_of proved_conclusion_with_old_vars aconv Thm.term_of conclusion)
      then error ("not aconv:\n"
        ^ @{make_string} (Thm.prop_of proved_conclusion_with_old_vars)
        ^ "\nand\n"
        ^ @{make_string} (Thm.term_of conclusion))
      else ()
  in
    proved_conclusion_with_old_vars
  end

and get_prems_and_lemmas ctxt clause_db origin =
  (get_premises ctxt clause_db origin, get_lemmas origin)

and get_premises _ _ (Jeha_Log.Axiom { thm = thm }) = [thm]
  | get_premises ctxt clause_db origin =
      let
        val ids_and_shifts_and_substituitons = Jeha_Log.premises_shift_substitution origin
        val instantiated_premises =
          ids_and_shifts_and_substituitons
          |> map (fn { id, shift, substitution } =>
              impl_reconstruct_with_metis ctxt clause_db id
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
      in
        instantiated_premises
      end

fun reconstruct_with_metis ctxt (clause_db : int -> JClause.T) id =
  impl_reconstruct_with_metis ctxt clause_db id


end;