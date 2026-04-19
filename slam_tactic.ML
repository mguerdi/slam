
signature SLAM_TACTIC =
sig
  type slam_options
  val slam_method : slam_options * thm list -> Proof.context -> thm list -> tactic
  val slam_tac : slam_options -> Proof.context -> term option -> thm list -> int -> tactic
  val parse_slam_options : slam_options parser
  val dump : (Slam.prover_state list) Unsynchronized.ref
  val reconstruct_proof : Slam.prover_state -> tactic
end

structure Slam_Tactic : SLAM_TACTIC =
struct
open Slam_Common

exception SLAM_UNIMPLEMENTED

(* METIS: type slam_options (string list option * string option) * thm list *)
type slam_options = string list

val dump = Unsynchronized.ref []

fun reconstruct_proof
      (state as
        { context = context,
          countdown = _,
          passive = passive,
          active = active,
          archive = archive,
          ... }: Slam.prover_state)
      _
    =
  let
    val SOME false_id =
      active
      |> Slam_Clause_Set.dest
      |> find_first JClause.is_false
      |> Slam_Common.map_some JClause.id
    val clause_db = Slam.make_clause_db state
    val false_proved =
      Slam_Proof.reconstruct context clause_db false_id
  in
    Seq.single (Goal.protect 0 false_proved)
  end

fun slam_tac options ctxt goal_term ths i st0 =
  let
    val _ = Slam_Common.validate_config ctxt
    val ctxt = Config.put Unify.search_bound (Config.get ctxt Slam_Common.unify_search_bound) ctxt
    (* tracing *)
    val _ = Slam_Common.trace_msg ctxt (fn () => "st0: " ^ @{make_string} st0)
    val _ = Slam_Common.trace_msg ctxt (fn () => "Thm.prop_of st0: " ^ @{make_string} (Thm.prop_of st0))
    val _ = Slam_Common.trace_msg ctxt (fn () =>
      "slam called with theorems:\n" ^ cat_lines (map (@{make_string}) ths))
    fun handle_exception (e, state) = 
      if exists (curry (op =) "dump") options
        then
          (let val _ = dump := state :: (!dump) in
            (writeln "EXCEPTION WAS RAISED! Prover state dumped to Slam_Tactic.dump"; raise e)
          end)
        else raise e
    fun contains_const name t =
      fold_aterms (fn (Const (name', _)) => (fn b => b orelse name = name') | _ => I) t false
    val atomized_ths = map (Conv.fconv_rule (Object_Logic.atomize ctxt)) ths
    fun tac ctxt' i' =
      (* FIXME: why are we doing this??? *)
      Subgoal.FOCUS (fn { context, prems, ...} => (fn st =>
          (* FIXME: make sure that we really don't need asms (only use is in
          HOL/Tools/Quotient/quotient_tacs.ML) *)
          let
            val simplify = Meson.presimplify Meson.simp_options_all_true context

            val already_presimplified = Config.get ctxt Slam_Common.meson
            val do_presimplify =
              not already_presimplified andalso Config.get ctxt Slam_Common.presimplify

            val initial_clauses =
              atomized_ths @ prems
              |> do_presimplify ? map simplify
          in
            case ((Slam_Common.cpu_time_milliseconds (Slam.try_saturate context goal_term) initial_clauses
                handle Slam.SLAM_EXCEPTION (e, state) => handle_exception (e, state))
                handle Exn.Interrupt_Breakdown => error "caught Interrupt_Breakdown") of
              ((Slam.Unsat, final_state), time) =>
                let val () =
                  writeln ("total elapsed time until contradiction: " ^ @{make_string} time ^ " ms")
                in
                  case Slam_Common.get_proof_reconstruction_mode context of
                    (* st is something like A \<Longrightarrow> B \<Longrightarrow> #False *)
                    (* we provide #False *)
                    Slam_Common.Cheat => ALLGOALS (Skip_Proof.cheat_tac context) st
                  | _ => reconstruct_proof final_state st
                end
            | ((Slam.MaybeSat, final_state), _) => Seq.empty
            | ((Slam.Next, final_state), _) => error "Bug: Next in final result"
          end
        )
      ) ctxt i' (* FIXME: why not ctxt'? *)
    val seq =
      (* SELECT_GOAL applies the tactic (it's first argument) to the selected
      subgoal, i.e. an element in the list
        goal (N subgoals):
          1. ...
          2. ...
          ... *)
      SELECT_GOAL
        (Object_Logic.atomize_prems_tac ctxt 1
          (* goal: A \<Longrightarrow> ... \<Longrightarrow> B *)
          THEN resolve_tac ctxt @{thms ccontr} 1
          (* goal: A \<Longrightarrow> ... \<Longrightarrow> \<not> B \<Longrightarrow> False *)
          THEN tac ctxt 1)
        i
        st0
  in
    seq
  end handle JClause.NOBOOL (msg, term, typ) => (Slam_Common.trace_msg ctxt (fn () => (msg ^ ". Term " ^ @{make_string} term ^ " of type " ^ @{make_string} typ)); Seq.empty)

(* from metis_tactic.ML *)
fun neg_clausify ctxt combinators =
  single
  #> Meson.make_clauses_unsorted ctxt
  #> combinators ? map (Meson_Clausify.introduce_combinators_in_theorem ctxt)
  #> Meson.finish_cnf true

fun preskolem_tac ctxt st0 =
  (if exists (Meson.has_too_many_clauses ctxt)
             (Logic.prems_of_goal (Thm.prop_of st0) 1) then
     Simplifier.full_simp_tac (Meson_Clausify.ss_only @{thms not_all not_ex} ctxt) 1
     THEN CNF.cnfx_rewrite_tac ctxt 1
   else
     all_tac) st0

(* Like Meson.MESON but properly threads context through to mkcl and cltac.
Avoids
  Bad context: clash of fresh free for bound: :000 vs. xa
exception.
*)
(*Basis of all meson-tactics.  Supplies cltac with clauses: HOL disjunctions.
  Function mkcl converts theorems to clauses.*)
fun CONTEXT_MESON preskolem_tac mkcl cltac ctxt i st =
  SELECT_GOAL
    (EVERY [Object_Logic.atomize_prems_tac ctxt 1,
            resolve_tac ctxt @{thms ccontr} 1,
            preskolem_tac,
            Subgoal.FOCUS (fn {context = ctxt', prems = negs, ...} =>
                      EVERY1 [Meson.skolemize_prems_tac Meson.simp_options_all_true ctxt' negs,
                              Subgoal.FOCUS
                                (fn { context = ctxt'', prems = prems, ... } =>
                                  cltac ctxt'' (mkcl ctxt'' prems)
                                )
                                ctxt']
                              ) ctxt 1]) i st
  handle THM _ => no_tac st;    (*probably from make_meta_clause, not first-order*)

fun slam_meson_tac options ctxt facts i: tactic =
  fn st =>
    let
      val () = writeln ("st: " ^ @{make_string} st)
      val concl = Thm.concl_of st
      val goal = the_default concl (concl |> try HOLogic.dest_Trueprop)
      val () = writeln ("goal: " ^ Slam_Common.pretty_term ctxt goal)
      (* Eliminate Ball, etc. *)
      fun simplify ctxt = Meson.presimplify Meson.simp_options_all_true ctxt
    in
    CONTEXT_MESON
      (preskolem_tac ctxt)
      (fn ctxt => maps (neg_clausify ctxt false))
      (fn ctxt => fn ths => slam_tac options ctxt (SOME goal) (map (simplify ctxt) (ths @ facts)) i)
      ctxt
      i
      st
    end

val has_tvar = exists_type (exists_subtype (fn TVar _ => true | _ => false)) o Thm.prop_of

fun slam_meson_method (options, ths) ctxt facts =
    let
      val (schem_facts, nonschem_facts) = List.partition has_tvar facts
    in
      HEADGOAL (Method.insert_tac ctxt nonschem_facts THEN'
        CHANGED_PROP o slam_meson_tac options ctxt (schem_facts @ ths))
    end

(* FIXME: only pass schematic facts to slam_tac? see metis_tactic.ML *)
fun slam_no_meson_method (options, ths) ctxt facts =
    HEADGOAL (slam_tac options ctxt NONE (facts @ ths))

fun slam_method (options, ths) ctxt facts =
  if Config.get ctxt Slam_Common.meson
    then slam_meson_method (options, ths) ctxt facts
    else slam_no_meson_method (options, ths) ctxt facts

(* utilities *)

(* by (slam (...) ...)
            ^^^^^      *)
val parse_slam_options =
  (* Scan.optional parses using it's first argument and returns it's second argument as default in
  case of failure *)
  Scan.optional
      (* |-- composes parsers but throws away results of the first one *)
      (* (Args.name -- Scan.option (\<^keyword>\<open>,\<close> |-- Args.name)) parses a comma seperated list of
      names *)
      (* FIXME: validate inputs while parsing not afterwards *)
      (Args.parens (Args.name -- Scan.repeat (\<^keyword>\<open>,\<close> |-- Args.name)) >> (uncurry cons))
      []


val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>slam\<close>
      (* Scan.lift to turns the parser parse_slam_options into a context_parser *)
      (* -- to pass the tokens left over by parse_slam_options to Attrib.thms and pair the
      resulting theorem list with parse_slam_options' parse result *)
      (* >> to apply (METHOD oo slam_method) the the previous parse result *)
      (Scan.lift parse_slam_options -- Attrib.thms >> (METHOD oo slam_method))
      "slam for FOL and HOL problems");

end


(*

(* metis_tac_unused : Proof.context -> thm list -> int -> thm -> thm Seq.seq *)
fun metis_tac_unused ctxt ths i st0 =
  let
    val _ = trace_msg ctxt (fn () =>
      "Metis called with theorems\n" ^ cat_lines (map (Thm.string_of_thm ctxt) ths))
    fun tac clause = resolve_tac ctxt (FOL_SOLVE ctxt clause ths) 1
    val seq = Meson.MESON (maps (neg_clausify ctxt)) tac ctxt i st0
  in
    (seq)
  end


(* MESON: (thm list -> thm list) -> (thm list -> tactic) -> Proof.context -> int -> tactic *)
(*Basis of all meson-tactics.  Supplies cltac with clauses: HOL disjunctions.
  Function mkcl converts theorems to clauses.*)
fun MESON mkcl cltac ctxt i st =
  SELECT_GOAL
    (Subgoal.FOCUS (fn {context = ctxt', prems = negs, ...} =>
              Subgoal.FOCUS (cltac o mkcl o #prems) ctxt' 1) ctxt 1) i st
  handle THM _ => no_tac st;    (*probably from make_meta_clause, not first-order*)

(* SELECT_GOAL : tactic -> int -> tactic *)
(* fun SELECT_GOAL method i = RESTRICT_GOAL i 1 method *)
(* fun RESTRICT_GOAL i n method =
     BYPASS_CONTEXT (PRIMITIVE (Goal.restrict i n)) THEN
     method THEN
     BYPASS_CONTEXT (PRIMITIVE (Goal.unrestrict i)); *)
(* EVERY : tactic list -> tactic *)
(* EVERY1 : (int -> tactic) list -> tactic *)
(* Subgoal.FOCUS: (focus -> tactic) -> Proof.context -> int -> tactic *)
(* type focus =
     { context: Proof.context
     , params: (string * cterm) list
     , prems: thm list
     , asms: cterm list
     , concl: cterm
     , schematics: ctyp TVars.table * cterm Vars.table
     }; *)

(* resolve_tac : Proof.context -> thm list -> int -> tactic *)
(* resolve_tac ctxt (FOL_SOLVE ctxt clause ths) 1 : tactic *)
(* FOL_SOLVE ctxt clause ths : thm list *)
(* FOL_SOLVE : Proof.context -> thm list -> thm list -> thm list *)
(* Main function to start Metis proof and reconstruction *)
fun FOL_SOLVE ctxt cls ths0 =
*)