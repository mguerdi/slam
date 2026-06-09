theory slam_tptp

imports SLAM.slam "HOL-TPTP.ATP_Problem_Import"

begin

ML\<open>
structure Slam_ATP_Problem_Import =
struct

fun print_szs_of_success conjs success =
  (
  writeln ("% SZS status " ^
    (if success then
       if null conjs then "Unsatisfiable" else "Theorem"
     else
       "GaveUp"));
  writeln "% Details "

  )

fun SOLVE_TIMEOUT seconds name tac st =
  let
    val _ = writeln ("running " ^ name ^ " for " ^ string_of_int seconds ^ " s")
    val result =
      Timeout.apply (Time.fromSeconds seconds) (fn () => SINGLE (SOLVE tac) st) ()
      handle
        Timeout.TIMEOUT e => (writeln ("FAILURE: " ^ name); raise Timeout.TIMEOUT e)
      | ERROR e => (writeln ("FAILURE: " ^ name); raise ERROR e)
  in
    (case result of
      NONE => (writeln ("FAILURE: " ^ name); Seq.empty)
    | SOME st' => (writeln ("SUCCESS: " ^ name); Seq.single st'))
  end

fun informative_can_tac ctxt tactic conj: thm Exn.result =
  Exn.capture (Goal.prove_internal ctxt [] (Thm.cterm_of ctxt conj)) (fn [] => tactic ctxt)

fun slam_tptp_file thy timeout file_name =
  let
    val (conjs, assms, lthy) = ATP_Problem_Import.read_tptp_file thy snd file_name
    val conj = ATP_Problem_Import.make_conj ([], []) conjs
    val assms = op @ assms
    val cassms = map (Thm.cterm_of lthy) assms
    (* make_thm doesn't work because it tries to certify the terms in the global thy instead of in
    lthy. *)
    val assm_ths0 = map (Skip_Proof.make_thm_cterm) cassms
    fun tac lthy =
      (Slam_Tactic.slam_tac [] lthy (SOME conj) assm_ths0)
      |> HEADGOAL
      |> SOLVE_TIMEOUT timeout "slam"
  in
    informative_can_tac lthy tac conj
    |> (fn res => case res of
          Exn.Res th => true
        | Exn.Exn e => (writeln ("% Exception: " ^ @{make_string} e); false)
        )
    |> print_szs_of_success conjs
  end

fun metis_lifting_tptp_file thy timeout file_name =
  let
    val (conjs, assms, lthy) = ATP_Problem_Import.read_tptp_file thy snd file_name
    val conj = ATP_Problem_Import.make_conj ([], []) conjs
    val assms = op @ assms
    val cassms = map (Thm.cterm_of lthy) assms
    (* make_thm doesn't work because it tries to certify the terms in the global thy instead of in
    lthy. *)
    val assm_ths0 = map (Skip_Proof.make_thm_cterm) cassms
    fun tac lthy =
      Metis_Tactic.metis_tac [] "lifting" lthy assm_ths0
      |> HEADGOAL
      |> SOLVE_TIMEOUT timeout "metis_lifting"
  in
    informative_can_tac lthy tac conj
    |> (fn res => case res of
          Exn.Res th => true
        | Exn.Exn e => (writeln ("% Exception: " ^ @{make_string} e); false)
        )
    |> print_szs_of_success conjs
  end

end
\<close>

end
