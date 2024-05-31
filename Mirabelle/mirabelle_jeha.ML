(* Based on HOL/Tools/Mirabelle/mirabelle_jeha.ML
* Modified to explicitly record timeouts in mirabelle.log. *) 

structure Mirabelle_Jeha: MIRABELLE_ACTION =
struct


fun can_apply_exn time tac st =
  let
    val {context = ctxt, facts, goal} = Proof.goal st;
    val full_tac = HEADGOAL (Method.insert_tac ctxt facts THEN' tac ctxt);
    (* raises Timeout.TIMEOUT *)
    val result = Timeout.apply time (Seq.pull o full_tac) goal
  in
    (case result of
      SOME _ => true
    | _ => false)
  end;

fun can_apply_msg time tac st =
  if can_apply_exn time tac st then "succeeded" else "failed" handle Timeout.TIMEOUT _ => "timeout"
  (* if can_apply_exn time tac st then "succeeded" else "failed" handle _ => "some exception" *)

fun make_action ({timeout, ...} : Mirabelle.action_context) =
  let
    fun run ({pre, post, ...} : Mirabelle.command) =
      let
        val thms = Mirabelle.theorems_of_sucessful_proof post;
        val names = map Thm.get_name_hint thms;
        val facts = map #1 (Facts.props (Proof_Context.facts_of (Proof.context_of pre)));
        fun jeha ctxt = Jeha_Tactic.jeha_tac [] ctxt (thms @ facts);
      in
        (* (if Mirabelle.can_apply timeout jeha pre then "succeeded" else "failed") *)
        (can_apply_msg timeout jeha pre)
        (* FIXME: include extra information like exception traces or jeha trace *)
        |> not (null names) ? suffix (":\n" ^ commas names)
      end
  in ("", {run = run, finalize = K ""}) end

val () = Mirabelle.register_action "jeha" make_action

end
