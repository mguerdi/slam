theory slam_tptp

imports SLAM.slam "HOL-TPTP.ATP_Problem_Import"

begin

ML\<open>

(*
fun triple_ord ord1 ord2 ord3 ((x1, x2, x3), (y1, y2, y3)) =
  prod_ord ord1 (prod_ord ord2 ord3) ((x1, (x2, x3)), (y1, (y2, y3)))

fun distinct_bunches ctxt =
  Sledgehammer_Prover.bunches_of_metis_methods ctxt false false
  @ Sledgehammer_Prover.bunches_of_metis_methods ctxt false true
  @ Sledgehammer_Prover.bunches_of_metis_methods ctxt true false
  @ Sledgehammer_Prover.bunches_of_metis_methods ctxt true true
  |> List.concat
  (* string option * string option * string list *)
  (* |> sort (fn (Sledgehammer_Proof_Methods.Metis_Method l, Sledgehammer_Proof_Methods.Metis_Method r) =>
    triple_ord (option_ord string_ord) (option_ord string_ord) (list_ord string_ord) (l, r)
  ) *)
  |> tap (fn x => writeln ("length=" ^ @{make_string} (length x)))
  |> distinct (fn (Sledgehammer_Proof_Methods.Metis_Method l, Sledgehammer_Proof_Methods.Metis_Method r) =>
    l = r
  )
  |> tap (fn x => writeln ("length=" ^ @{make_string} (length x)))

val bs = distinct_bunches @{context}

val _ = map (writeln o @{make_string}) bs
*)

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


(* type_encs \<in> {"full_types, no_types, mono_tags"} *)
(* lam_tras \<in> {""} *)
(*

(PREFERRED_METHSS
(
  (Metis_Method (NONE) (NONE) (LIST))
  (LIST
    (LIST (Dynamic_Method slam))
    (LIST (Metis_Method (NONE) (NONE) (LIST)))
    (LIST)
    (LIST
      (Metis_Method (SOME full_types) (NONE) (LIST))
      (Metis_Method (NONE) (SOME lifting) (LIST))
      (Metis_Method (SOME mono_tags) (SOME lifting) (LIST))
      (Metis_Method (SOME no_types) (SOME lifting) (LIST))
    )
    (LIST
      (Metis_Method (NONE) (SOME lifting) (LIST ext))
      (Metis_Method (SOME no_types) (SOME lifting) (LIST ext))
    )
    (LIST)
    (LIST)
    (LIST)
    (LIST)
  )
))

*)

fun tac_of_metis ctxt (type_enc_opt, lam_trans_opt) =
  let
    (* FIXME: ext? *)
    (* val additional_facts = maps (thms_of_name ctxt) additional_fact_names *)
    val additional_facts = []
    val global_facts = []
    val local_facts = []
    val ctxt = ctxt
      |> Config.put Metis_Tactic.verbose false
      |> Config.put Metis_Tactic.trace false
  in
    SELECT_GOAL (Metis_Tactic.metis_method ((Option.map single type_enc_opt, lam_trans_opt),
      additional_facts @ global_facts) ctxt local_facts)
  end

val ext_name = "HOL.ext"

val ext = @{thm ext}

(* Generated using from bunches_of_metis_methods using distinct_bunches above. *)
val metis_variants =
  [ Sledgehammer_Proof_Methods.Metis_Method (NONE, NONE, [])
  , Sledgehammer_Proof_Methods.Metis_Method (SOME "full_types", NONE, [])
  , Sledgehammer_Proof_Methods.Metis_Method (NONE, SOME "lifting", [])
  , Sledgehammer_Proof_Methods.Metis_Method (SOME "mono_tags", SOME "opaque_lifting", [])
  , Sledgehammer_Proof_Methods.Metis_Method (SOME "no_types", SOME "opaque_lifting", [])
  , Sledgehammer_Proof_Methods.Metis_Method (NONE, SOME "lifting", [ext_name])
  , Sledgehammer_Proof_Methods.Metis_Method (SOME "mono_tags", SOME "lifting", [])
  , Sledgehammer_Proof_Methods.Metis_Method (SOME "no_types", SOME "lifting", [])
  , Sledgehammer_Proof_Methods.Metis_Method (SOME "no_types", SOME "lifting", [ext_name])
  , Sledgehammer_Proof_Methods.Metis_Method (SOME "mono_tags", NONE, [])
  , Sledgehammer_Proof_Methods.Metis_Method (SOME "full_types", SOME "opaque_lifting", [])
  , Sledgehammer_Proof_Methods.Metis_Method (SOME "full_types", SOME "lifting", [])
  , Sledgehammer_Proof_Methods.Metis_Method (SOME "full_types", SOME "lifting", [ext_name])
  ]

(* The first parameter `variant` controls the variant of metis used. It's always of the form metisN.
with some number N. There are 13 variants, each variant can be run with the facts passed as local or
global, so N ranges from 0 to 25 = 2 * 13 - 1. *)
fun metis_tptp_file metis_variant thy timeout file_name =
  let
    val (conjs, assms, lthy) = ATP_Problem_Import.read_tptp_file thy snd file_name
    val conj = ATP_Problem_Import.make_conj ([], []) conjs
    val assms = op @ assms
    val cassms = map (Thm.cterm_of lthy) assms
    (* make_thm doesn't work because it tries to certify the terms in the global thy instead of in
    lthy. *)
    val assm_ths0 = map (Skip_Proof.make_thm_cterm) cassms

    val index_str = unprefix "metis" metis_variant
    val SOME index = Int.fromString index_str
    val metis_variant = nth metis_variants (index div 2)
    val local_only = index mod 2 = 0
    val facts =
      if local_only
        then (assm_ths0, []) (* all local *)
        else ([], assm_ths0) (* all global *)
    val () = writeln (
      "% Metis variant: " ^ @{make_string} metis_variant ^
      " (" ^ (if local_only then "local facts" else "global fact") ^ ")"
    )

    fun tac lthy =
      Sledgehammer_Proof_Methods.tac_of_proof_method lthy facts metis_variant
      |> HEADGOAL
      |> SOLVE_TIMEOUT timeout ("metis" ^ @{make_string} index)
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
