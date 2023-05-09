
signature JEHA_TACTIC =
sig
  type jeha_options
  val jeha_method : jeha_options * thm list -> Proof.context -> thm list -> tactic
  val jeha_tac : jeha_options -> Proof.context -> thm list -> int -> tactic
  val parse_jeha_options : jeha_options parser
  val dump : ((Proof.context * int * Jeha.Passive_Set.T * JClause.T list) list) Unsynchronized.ref
end

structure Jeha_Tactic : JEHA_TACTIC =
struct
open Jeha_Common

exception JEHA_UNIMPLEMENTED

(* METIS: type jeha_options (string list option * string option) * thm list *)
type jeha_options = string list

val dump = Unsynchronized.ref []

fun jeha_tac options ctxt ths i st0 =
  let
    val _ = Jeha_Common.trace_msg ctxt (fn () => "st0: " ^ @{make_string} st0)
    val _ = Jeha_Common.trace_msg ctxt (fn () => "Thm.prop_of st0: " ^ @{make_string} (Thm.prop_of st0))
    val seq =
      case Thm.prop_of st0 of
        (* FIXME: this handles the TERM _ call from Isar, but why do we need to do this?? *)
        (Const ("Pure.prop", _) $ (Const ("Pure.term", _) $ _)) => Seq.single st0
      | _ =>
        let
          val _ = Jeha_Common.trace_msg ctxt (fn () =>
            "jeha called with theorems\n" ^ cat_lines (map (Thm.string_of_thm ctxt) ths))
        in
          (* if Jeha.refutable ctxt ths st0 then ALLGOALS (Skip_Proof.cheat_tac ctxt) st0 else Seq.empty *)
          (* FIXME: why are we doing this??? *)
          Subgoal.FOCUS (fn { context, prems, asms, concl, ...} => (fn st =>
            (* FIXME: asms and prems seems to be the same *)
            if Jeha.refutable context (prems @ ths) asms (Thm.term_of concl)
                handle Jeha.JEHA_EXCEPTION (e, state) =>
                  (if exists (curry (op =) "dump") options
                    then
                      (let val _ = dump := state :: (!dump) in
                        (writeln "EXCEPTION WAS RAISED! Prover state dumped to Jeha_Common.dump"; raise e)
                      end)
                    else raise e)
              then ALLGOALS (Skip_Proof.cheat_tac context) st
              else Seq.empty)
          ) ctxt i st0
        end
  in
    seq
  end

(* FIXME: only pass schematic facts to jeha_tac? see metis_tactic.ML *)
fun jeha_method (options, ths) ctxt facts =
    HEADGOAL (jeha_tac options ctxt (facts @ ths))

(* utilities *)

(* by (jeha (...) ...)
            ^^^^^      *)
val parse_jeha_options =
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
    (Method.setup \<^binding>\<open>jeha\<close>
      (* Scan.lift to turns the parser parse_jeha_options into a context_parser *)
      (* -- to pass the tokens left over by parse_jeha_options to Attrib.thms and pair the
      resulting theorem list with parse_jeha_options' parse result *)
      (* >> to apply (METHOD oo jeha_method) the the previous parse result *)
      (Scan.lift parse_jeha_options -- Attrib.thms >> (METHOD oo jeha_method))
      "jeha for FOL and HOL problems");

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