(* Mostly lifted from argo_tactic.ML to fix issue with undeclared hyps. *)

signature JEHA_ARGO =
sig
  val repaired_argo_tac : Proof.context -> thm list -> int -> tactic
end

structure Jeha_Argo: JEHA_ARGO =
struct
  
(* normalizing goals *)

fun instantiate v ct = Thm.instantiate (TVars.empty, Vars.make1 (v, ct))

fun instantiate_elim_rule thm =
  let
    val ct = Drule.strip_imp_concl (Thm.cprop_of thm)
  in
    (case Thm.term_of ct of
      \<^Const_>\<open>Trueprop for \<open>Var (v as (_, \<^Type>\<open>bool\<close>))\<close>\<close> => instantiate v \<^cterm>\<open>False\<close> thm
    | Var v => instantiate v \<^cprop>\<open>False\<close> thm
    | _ => thm)
  end

fun atomize_conv ctxt ct =
  (case Thm.term_of ct of
    \<^Const_>\<open>Trueprop for _\<close> => Conv.all_conv
  | \<^Const_>\<open>Pure.imp for _ _\<close> =>
      Conv.binop_conv (atomize_conv ctxt) then_conv
      Conv.rewr_conv @{thm atomize_imp}
  | \<^Const>\<open>Pure.eq _ for _ _\<close> =>
      Conv.binop_conv (atomize_conv ctxt) then_conv
      Conv.rewr_conv @{thm atomize_eq}
  | \<^Const>\<open>Pure.all _ for \<open>Abs _\<close>\<close> =>
      Conv.binder_conv (atomize_conv o snd) ctxt then_conv
      Conv.rewr_conv @{thm atomize_all}
  | _ => Conv.all_conv) ct

fun normalize ctxt thm =
  thm
  |> instantiate_elim_rule
  |> Conv.fconv_rule (Thm.beta_conversion true then_conv Thm.eta_conversion)
  |> Thm.forall_intr_vars
  |> Conv.fconv_rule (atomize_conv ctxt)

(* timeout *)

val timeout = Attrib.setup_config_real \<^binding>\<open>argo_timeout\<close> (K 10.0)

val timeout_seconds = seconds o Config.apply timeout

fun with_timeout f ctxt = Timeout.apply (timeout_seconds ctxt) f ctxt

(*  Turn
      False  [A', ...]
    where
      A' = (normalize A ctxt)
    is an undeclared hyp because the correct hyp would be A (\<in> prems) into
      False  [A, ...]
    and then using implies_intr to get
      A' \<Longrightarrow> False  [...]
    and finally implies_elim with A'  [A] (which is obtained by applying normalize to A  [A]) to get
      False  [A, ...]
*)
fun argo_repair_undeclared_hyps ctxt prems thm =
  let
    val undeclared_hyps = Thm.undeclared_hyps (Context.Proof ctxt) thm
    val () = tracing ("REPAIR: undeclared_hyps = " ^ Pretty.string_of (Pretty.list "[" "]" (map (Syntax.pretty_term ctxt) undeclared_hyps)))
    (* undecl_hyp1 \<Longrightarrow> undecl_hyp2 \<Longrightarrow> ... \<Longrightarrow> False  [**decl_hyps] *)
    val thm_implied_by_undeclared_hyps = fold (Thm.implies_intr o Thm.cterm_of ctxt) undeclared_hyps thm
    val () = tracing ("REPAIR: thm_implied_by_undeclared_hyps = " ^ @{make_string} thm_implied_by_undeclared_hyps)
    (* Hyp  [Hyp] \<mapsto> $(normalize ctxt Hyp)  [Hyp] *)
    (* Hyps is the declared hyp, normalize ... is the undeclared version of that Hyp *)
    
    (* FIXME: normalize isn't all that's  happening. In the example
      lemma and_elim:
        shows "A \<and> B \<Longrightarrow> (A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> C"
        by (jeha)
    we have an undeclared hyp \<not>\<not>B and a normalized premise B \<noteq> False.
    *)
    val argo_normalized_prems = map (normalize ctxt) prems
    val argo_normalized_prems_terms = map Thm.prop_of argo_normalized_prems
    val () = tracing ("REPAIR: argo_normalized_prems" ^ @{make_string} argo_normalized_prems)
    val () = tracing ("REPAIR: undeclared_hyps" ^ @{make_string} undeclared_hyps)
    val undecl_hyp_idx_to_prem_idx = map (fn hyp => find_index (fn argo_normed_prem => hyp aconv argo_normed_prem) argo_normalized_prems_terms) undeclared_hyps
    val () = tracing ("REPAIR: undecl_hyp_idx_to_prem_idx" ^ @{make_string} undecl_hyp_idx_to_prem_idx)
    val undeclared_hyps_prems = fold (fn idx => fn acc => nth argo_normalized_prems idx :: acc) undecl_hyp_idx_to_prem_idx []
    val () = tracing ("REPAIR: undeclared_hyps_prems" ^ @{make_string} undeclared_hyps_prems)
  in
    fold (fn x => fn y => Thm.implies_elim y x) undeclared_hyps_prems thm_implied_by_undeclared_hyps
  end

fun repaired_argo_tac ctxt thms =
  CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1
    (Conv.try_conv (Conv.rewr_conv @{thm atomize_eq})))) ctxt)
  THEN' resolve_tac ctxt [@{thm ccontr}]
  THEN' Subgoal.FOCUS (fn {context = ctxt', prems, ...} =>
    (case with_timeout (Argo_Tactic.prove (thms @ prems)) ctxt' of
      (SOME thm, _) =>
        resolve_tac ctxt' [thm] 1
        (* NEW *)
        THEN PRIMITIVE (argo_repair_undeclared_hyps ctxt' prems)
    | (NONE, _) => no_tac)) ctxt

end