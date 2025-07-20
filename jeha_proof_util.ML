signature JEHA_PROOF_UTIL =
sig
  val comp_no_flatten_no_incr: thm * int -> int -> thm -> thm
  val norm_negative_predicate_literals: Proof.context -> thm -> thm 
  val envir_norm_thm : Proof.context -> Envir.env -> thm -> thm
  val envir_subst_thm : Proof.context -> Type.tyenv * Envir.tenv -> thm -> thm
  val with_fixed_vars : cterm list -> ctyp list -> Proof.context -> tactic -> tactic
  val with_all_vars_fixed : Proof.context -> tactic -> tactic
  val thm_to_not_imp_false : thm -> thm
  (* 1-based *)
  val make_prem_last : int -> thm -> thm
  val move_last_prem_to : int -> thm -> thm
  val move_prem_from_to : int -> int -> thm -> thm
  val move_prems_left : int -> int -> int -> thm -> thm
end

structure Jeha_Proof_Util : JEHA_PROOF_UTIL =
struct

(* Drule.comp_no_flatten but without incr_indexes *)
(* n : number of protected premises of lhs *)
(* i : 1-based index of premise in the rhs that the conclusion of the lhs is matched against. *)
(* result: rule but with the i-th (1-based) premise replace by the protected premises of lhs. *)
(* A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D    E \<Longrightarrow> (C \<Longrightarrow> D) \<Longrightarrow> F *)
(*       ^ n=2                      ^ i=2 *)
(* ----------------------------------------------- *)
(* E \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> F *)
fun comp_no_flatten_no_incr (th, n) i rule =
  (case distinct Thm.eq_thm (Seq.list_of
      (Thm.bicompose NONE {flatten = false, match = false, incremented = true}
        (false, th, n) i rule)) of
    [th'] => Thm.solve_constraints th'
  | [] => raise THM ("comp_no_flatten", i, [th, rule])
  | _ => raise THM ("comp_no_flatten: unique result expected", i, [th, rule]));

fun norm_negative_predicate_literals ctxt th =
  let
    (* guards against normalizing literals where the normalization is not a permitted simplification *)
    (* serves as an "override" *)
    fun guard_tac i =
      let
        fun do_guard st =
          let
            (* negated literal *)
            val (s, t, b) = JLit.of_term (HOLogic.dest_Trueprop (the_single (Thm.prems_of st)))
            val lit = (s, t, not b)
            val normed_lit = JLit.norm_negative_pred ctxt lit
          in
            if lit = normed_lit
              then all_tac st
              else no_tac st
          end
      in
        SELECT_GOAL do_guard i
      end
    val norm_tac =
      [ @{lemma "True \<noteq> False \<Longrightarrow> False = False" by auto}
      , @{lemma "True \<noteq> t \<Longrightarrow> False = t" by auto}
      , @{lemma "False \<noteq> t \<Longrightarrow> True = t" by auto}
      , @{lemma "s \<noteq> True \<Longrightarrow> s = False" by auto}
      , @{lemma "s \<noteq> False \<Longrightarrow> s = True" by auto} ]
      |> map (fn lemma => (resolve_tac ctxt [lemma]))
    val tac = FIRST' (guard_tac :: norm_tac)
  in
    Seq.hd (ALLGOALS (TRY o tac) th)
  end

(* Compare: Envir.subst_\<dots> *)
fun envir_subst_thm ctxt (tyenv, tenv) th =
  let
    val _ = Jeha_Common.trace_msg ctxt (fn () =>
      "envir_subst_thm: \n\t" ^
      Thm.string_of_thm ctxt th ^
      "\nwith environment\n\t" ^
      Jeha_Common.pretty_tenv ctxt (tenv) ^
      "\n\t" ^
      Jeha_Common.pretty_tyenv ctxt (tyenv))

    fun mkT (v, (S, T)) = ((v, S), Thm.ctyp_of ctxt (Envir.subst_type tyenv T))
    fun mk (v, (T, t)) =
      (* FIXME: why only Envir.subst_term_types and not Envir.subst_term? (The latter didn't work) *)
      (* Envir.subst_term_types on the r.h.s. applies the tyenv only to the types occuring in t.
      Reason: (tyenv, tenv) are substitutions where chasing is not necessary (or correct). The code
      below mimics what subst_term2 from envir.ML does.
      (FIXME: this last claim is not true. Looking at flexflex_first_order again, perhaps I should
      just leave t alone. ) *)
      ((v, Envir.subst_type tyenv T), Thm.cterm_of ctxt ((* Envir.subst_term_types tyenv *) t))

    val instsT = Vartab.fold (cons o mkT) tyenv []
    val insts = Vartab.fold (cons o mk) tenv []
  in
    Thm.instantiate (TVars.make instsT, Vars.make insts) th
  end

(* compare: Envir.norm_\<dots> *)
fun envir_norm_thm ctxt env th =
  (* see metis_reconstruct.ML, flexflex_first_order *)
  let
    val tyenv = Envir.type_env env
    val tenv = Envir.term_env env 
    val _ = Jeha_Common.trace_msg ctxt (fn () =>
      "envir_norm_thm: \n\t" ^
      Thm.string_of_thm ctxt th ^
      "\nwith environment\n\t" ^
      Jeha_Common.pretty_tenv ctxt (tenv) ^
      "\n\t" ^
      Jeha_Common.pretty_tyenv ctxt (tyenv))

    fun mkT (v, (S, T)) = ((v, S), Thm.ctyp_of ctxt (Envir.norm_type tyenv T))
    fun mk (v, (T, t)) = ((v, Envir.norm_type tyenv T), Thm.cterm_of ctxt (Envir.norm_term env t))

    val instsT = Vartab.fold (cons o mkT) tyenv []
    val insts = Vartab.fold (cons o mk) tenv []
  in
    Thm.instantiate_beta (TVars.make instsT, Vars.make insts) th
    |> Drule.eta_contraction_rule
    |> norm_negative_predicate_literals ctxt
  end

fun with_fixed_vars vars tvars ctxt tac th =
  let
    (* refls: ?A = ?A, ?B = ?B, ... *)
    val refls_of_old_vars = map Thm.reflexive vars 
    val refls_of_old_tvars_themselves =
      map (fn tvar => Thm.reflexive \<^instantiate>\<open>'a=tvar in cterm \<open>TYPE('a)\<close>\<close>) tvars
    val refls_old = refls_of_old_vars @ refls_of_old_tvars_themselves

    (* Fix all variable names. *)
    (* refls: _A = _A, _B = _B, ... *)
    val ((tables, (th_fixed :: refls_fixed)), ctxt_fixed) =
      Variable.import false (th :: refls_old) ctxt

    (* Replaced Free's by Var's and rename back to the original variable names. *)
    fun export_and_rename proved_th_fixed =
      let
        (* refls: ?A2 = ?A, ?B4 = ?B4, ... (have been renamed which we want to undo) *)
        val proved_th :: refls_new =
          Variable.export ctxt_fixed ctxt (proved_th_fixed :: refls_fixed)

        val () = \<^assert> (length refls_old = length refls_new)
        (* Doesn't work with Unify.matchers *)
        val new_to_old_matcher =
          fold
            (Pattern.first_order_match (Proof_Context.theory_of ctxt))
            (ListPair.zip (apply2 (map Thm.prop_of) (refls_new, refls_old)))
            (Vartab.empty, Vartab.empty)
        
        val proved_th_repaired = envir_subst_thm ctxt new_to_old_matcher proved_th
      in
        proved_th_repaired
      end
  in
    tac th_fixed
    |> Seq.map export_and_rename
  end

(* Fixes variables in the state, applies the tactic, regeneralizes the fixed vars, attempts to make
sure the variable names are the same ones as in the original state *)
fun with_all_vars_fixed ctxt (tac: tactic) th =
  let
    val vars = map #2 (Vars.dest (Thm.add_vars th Vars.empty))
    val tvars = map #2 (TVars.dest (Thm.add_tvars th TVars.empty))
  in
    with_fixed_vars vars tvars ctxt tac th
  end

(* Turn P into \<not>P \<Longrightarrow> False *)
fun thm_to_not_imp_false th =
  let
    val result = th COMP_INCR @{thm cnf.clause2raw_notE}
    (* Extract P from \<not>P \<Longrightarrow> False *)
    val t =
      result 
      |> Thm.prems_of
      |> the_single
      |> HOLogic.dest_Trueprop 
      |> HOLogic.dest_not 
    val t' =
      th
      |> Thm.prop_of
      |> HOLogic.dest_Trueprop
  in
    (* check if COMP_INCR broke any schematic variables *)
    if t aconv t'
      then result
      else error ("thm_to_not_imp_false")
  end

(* With index 1 turn A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> False into B \<Longrightarrow> C \<Longrightarrow> A \<Longrightarrow> False *)
(*Permute a rule's premises to move the i-th premise to the last position.*)
fun make_prem_last i th =
  let
    val n = Thm.nprems_of th
  in
    (* from metis_reconstruct.ML *)
    if i >= 1 andalso i <= n then Thm.permute_prems (i - 1) 1 th
    else raise THM ("make_last", i, [th])
  end

(* Like make_last but rotate right by one instead of left. *)
fun move_last_prem_to i th =
  let
    val n = Thm.nprems_of th
  in
    if i >= 1 andalso i <= n then Thm.permute_prems (i - 1) ~1 th
    else raise THM ("move_last_to", i, [th])
  end

fun move_prem_from_to (from: JClause.cpos) (to: JClause.cpos) =
  move_last_prem_to to o make_prem_last from

fun move_prems_left from number by th =
  if number < 0 then error "move_prems_left: can't move less than 0 literals" else
  if by < 0 then error "move_prems_left: can't move by negative amount" else
  if from + number > Thm.nprems_of th + 1
    then error "move_prems_left: prems to be moved go beyond end of clause" else
  if from - by < 1 then
    error ("move_prems_left: can't move prems beyond left end of clause "
      ^ @{make_string} (from, number, by, th))
  else
  fold (fn i => move_prem_from_to i (i - by)) (from upto (from + number - 1)) th

end