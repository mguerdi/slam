
signature SLAM_COMMON =
sig
  (* overrides all other tracing settings *)
  val trace : bool Config.T
  (* output the active set whenver it changes *)
  val trace_active : bool Config.T
  (* output 10 passive clauses at each step *)
  val trace_passive : bool Config.T

  (* override slam_trace during the respective phases *)
  val trace_forward_simp : bool Config.T
  val trace_backward_simp : bool Config.T
  val trace_cheap_simp : bool Config.T

  (* output archive *)
  val trace_archive : bool Config.T
  (* output inferred / new clauses *)
  val trace_inferred : bool Config.T

  (* trace rules (more fine grained control) *)
  val trace_sup : bool Config.T
  val trace_e_res : bool Config.T
  val trace_imitate_project : bool Config.T
  val trace_e_fact : bool Config.T
  val trace_arg_cong : bool Config.T
  val trace_bool_hoist : bool Config.T
  val trace_false_elim : bool Config.T
  val trace_eq_hoist : bool Config.T
  val trace_neq_hoist : bool Config.T
  val trace_forall_hoist : bool Config.T
  val trace_exists_hoist : bool Config.T
  val trace_bool_rw : bool Config.T
  val trace_forall_rw : bool Config.T
  val trace_exists_rw : bool Config.T
  val trace_neg_ext : bool Config.T
  val trace_neg_cong_fun : bool Config.T
  val trace_delete_duplicated_lits : bool Config.T
  val trace_delete_resolved_lits : bool Config.T
  val trace_destructive_e_res : bool Config.T
  val trace_rewrite_lits : bool Config.T
  val trace_positive_simplify_reflect : bool Config.T
  val trace_negative_simplify_reflect : bool Config.T
  val trace_simp_outer_claus : bool Config.T
  val trace_bool_simp : bool Config.T
  val trace_simp_false_elim : bool Config.T
  val trace_syntactic_tautology_deletion1 : bool Config.T
  val trace_syntactic_tautology_deletion2 : bool Config.T
  val trace_clause_subsumption : bool Config.T
  val trace_equality_subsumption : bool Config.T

  val trace_detailed_origin : bool Config.T

  (* report how many milliseconds the given clause procedure took to find a contradiction *)
  val report_main_loop_timing : bool Config.T

  val trace_rule_timing : bool Config.T
  val trace_all_rule_timings : bool Config.T

  val time_rule : Proof.context -> bool Config.T -> ('a -> 'b) -> 'a -> 'b

  val trace_msg : Proof.context -> (unit -> string) -> unit
  val trace_msg_active : Proof.context -> (unit -> string) -> unit
  val trace_msg_passive : Proof.context -> (unit -> string) -> unit
  val trace_msg_forward_simp : Proof.context -> (unit -> string) -> unit
  val trace_msg_backward_simp : Proof.context -> (unit -> string) -> unit
  val trace_msg_cheap_simp : Proof.context -> (unit -> string) -> unit
  val trace_msg_archive : Proof.context -> (unit -> string) -> unit
  val trace_msg_inferred : Proof.context -> (unit -> string) -> unit

  val trace_msg_sup : Proof.context -> (unit -> string) -> unit
  val trace_msg_e_fact : Proof.context -> (unit -> string) -> unit
  val trace_msg_e_res : Proof.context -> (unit -> string) -> unit
  val trace_msg_imitate_project : Proof.context -> (unit -> string) -> unit
  val trace_msg_arg_cong : Proof.context -> (unit -> string) -> unit
  val trace_msg_bool_hoist : Proof.context -> (unit -> string) -> unit
  val trace_msg_false_elim : Proof.context -> (unit -> string) -> unit
  val trace_msg_eq_hoist : Proof.context -> (unit -> string) -> unit
  val trace_msg_neq_hoist : Proof.context -> (unit -> string) -> unit
  val trace_msg_forall_hoist : Proof.context -> (unit -> string) -> unit
  val trace_msg_exists_hoist : Proof.context -> (unit -> string) -> unit
  val trace_msg_bool_rw : Proof.context -> (unit -> string) -> unit
  val trace_msg_forall_rw : Proof.context -> (unit -> string) -> unit
  val trace_msg_exists_rw : Proof.context -> (unit -> string) -> unit
  val trace_msg_neg_ext : Proof.context -> (unit -> string) -> unit
  val trace_msg_neg_cong_fun : Proof.context -> (unit -> string) -> unit
  val trace_msg_delete_duplicated_lits : Proof.context -> (unit -> string) -> unit
  val trace_msg_delete_resolved_lits : Proof.context -> (unit -> string) -> unit
  val trace_msg_destructive_e_res : Proof.context -> (unit -> string) -> unit
  val trace_msg_flex_flex_simp : Proof.context -> (unit -> string) -> unit
  val trace_msg_rewrite_lits : Proof.context -> (unit -> string) -> unit
  val trace_msg_positive_simplify_reflect : Proof.context -> (unit -> string) -> unit
  val trace_msg_negative_simplify_reflect : Proof.context -> (unit -> string) -> unit
  val trace_msg_simp_outer_claus : Proof.context -> (unit -> string) -> unit
  val trace_msg_bool_simp : Proof.context -> (unit -> string) -> unit
  val trace_msg_simp_false_elim : Proof.context -> (unit -> string) -> unit
  (*
  val trace_msg_syntactic_tautology_deletion1 : Proof.context -> (unit -> string) -> unit
  val trace_msg_syntactic_tautology_deletion2 : Proof.context -> (unit -> string) -> unit
  *)
  val trace_msg_clause_subsumption : Proof.context -> (unit -> string) -> unit
  val trace_msg_equality_subsumption : Proof.context -> (unit -> string) -> unit

  val init_config : Proof.context -> Proof.context

  val validate_config : Proof.context -> unit

  val proof_reconstruction : string Config.T
  datatype proof_reconstruction_mode = Cheat | Argo | Metis | Blast | Manual
  val get_proof_reconstruction_mode : Proof.context -> proof_reconstruction_mode

  val term_pat_setup : theory -> theory
  val type_pat_setup : theory -> theory
  val term_schem_setup : theory -> theory
  val verbose_of : Proof.context -> Proof.context
  val label_pretty : string -> Pretty.T -> Pretty.T
  val pretty_term : Proof.context -> term -> string
  val pretty_term' : Proof.context -> term -> Pretty.T
  val pretty_typ : Proof.context -> typ -> string
  val pretty_terms' : Proof.context -> term list -> Pretty.T
  val pretty_terms : Proof.context -> term list -> string
  val pretty_tyenv' : Proof.context -> Type.tyenv -> Pretty.T
  val pretty_tyenv : Proof.context -> Type.tyenv -> string
  val pretty_tenv' : Proof.context -> Envir.tenv -> Pretty.T
  val pretty_tenv : Proof.context -> Envir.tenv -> string
  val pretty_env' : Proof.context -> Envir.env -> Pretty.T
  val pretty_env : Proof.context -> Envir.env -> string
  val pretty_preunifier' : Proof.context -> Envir.env * (term * term) list -> Pretty.T
  val pretty_preunifier : Proof.context -> Envir.env * (term * term) list -> string
  val raw_pp_typ : typ -> Pretty.T
  val raw_pp_term : term -> Pretty.T
  val I : 'a -> 'a
  val map_some : ('a -> 'b) -> 'a option -> 'b option
  val some_is : ('a -> bool) -> 'a option -> bool
  val seq_cartesian_product : 'a Seq.seq -> 'b Seq.seq -> ('a * 'b) Seq.seq
  val cartesian_product : 'a list -> 'b list -> ('a * 'b) list
  val max_number_of_steps : int Config.T

  type smart_value = bool option
  val put_smart : string Config.T * bool -> Proof.context -> Proof.context
  val put_smarts : (string Config.T * bool) list -> Proof.context -> Proof.context
  val get_smart : Proof.context -> string Config.T -> smart_value (* "smart" => NONE *)
  val get_smart_default : Proof.context -> string Config.T -> bool (* "smart" => true *)

  (* Some configuration options, such as disable_all are handled by init_config and cause "smart"
  options to be overwritten, unless they have been explicitly set to a value different from "smart",
  in which case they are left alone and a warning is reported. *)

  val disable_all : bool Config.T

  type ho_unification_strategy
  val ho_unification_strategy : string Config.T
  val get_ho_unification_strategy : Proof.context -> ho_unification_strategy

  (* enable/disable individual rules *)
  val rule_enabled : Proof.context -> string Config.T -> bool

  (* inferences *)
  val rule_sup : string Config.T
  val rule_fluid_sup : string Config.T
  val rule_e_res : string Config.T
  val rule_imitate_project : string Config.T
  val rule_e_fact : string Config.T
  val rule_arg_cong : string Config.T
  val rule_bool_hoist : string Config.T
  val rule_false_elim : string Config.T
  val rule_eq_hoist : string Config.T
  val rule_neq_hoist : string Config.T
  val rule_forall_hoist : string Config.T
  val rule_exists_hoist : string Config.T
  val rule_bool_rw : string Config.T
  val rule_forall_rw : string Config.T
  val rule_exists_rw : string Config.T
  val rule_fluid_bool_hoist : string Config.T
  val rule_fluid_loob_hoist : string Config.T
  val rule_ext : string Config.T
  val rule_neg_ext : string Config.T
  val rule_neg_cong_fun : string Config.T
  val rule_choice : string Config.T
  (* simplifications *)
  val rule_delete_duplicated_lits : string Config.T
  val rule_delete_resolved_lits : string Config.T
  val rule_destructive_e_res : string Config.T
  val rule_flex_flex_simp : string Config.T
  val rule_rewrite_lits : string Config.T
  val rule_positive_simplify_reflect : string Config.T
  val rule_negative_simplify_reflect : string Config.T
  val rule_simp_outer_claus : string Config.T
  val rule_bool_simp : string Config.T
  val rule_simp_false_elim : string Config.T
  val rule_syntactic_tautology_deletion1 : string Config.T
  val rule_syntactic_tautology_deletion2 : string Config.T
  val rule_clause_subsumption : string Config.T
  val rule_equality_subsumption : string Config.T

  val delayed_unification : string Config.T
  val delayed_unification_simpl_only : string Config.T

  val unifier_cutoff : int Config.T
  val get_unifier_cutoff : Proof.context -> int

  val arg_cong_extra_conclusions : int Config.T
  val get_arg_cong_extra_conclusions : Proof.context -> int

  val select_negativoid : bool Config.T
  val select_flex_sided : bool Config.T
  val literal_selection_function : string Config.T

  val restricted_destructive_e_res : bool Config.T

  val clause_selection_heuristic : string Config.T
  datatype clause_selection_heuristic = Default | DelayedSimpOnlyUnification
  val get_clause_selection_heuristic : Proof.context -> clause_selection_heuristic

  val sup_variable_condition : string Config.T
  datatype sup_variable_condition = None | FirstOrder | Approximate
  val get_sup_variable_condition : Proof.context -> sup_variable_condition

  val neg_cong_fun_reveal_variable_headed : bool Config.T

  val bool_simp_quantifiers : bool Config.T
  val bool_simp_if_then_else : bool Config.T

  val forward_rewrite_countdown : int Config.T

  val arg_cong_as_simpl : bool Config.T
  val neg_ext_as_simpl : bool Config.T

  val presimplify : bool Config.T
  val meson : bool Config.T

  (* These cases would normally be handled by FluidSup *)
  val sup_into_fluid : bool Config.T
  val sup_into_deeply_occuring : bool Config.T
  val sup_into_non_eligible : bool Config.T
  val sup_from_non_eligible : bool Config.T

  val unify_search_bound : int Config.T
  val unify_timeout_ms : int Config.T
  val unify_matchcopy_fuel : int Config.T
  val supress_unify_trace : bool Config.T

  val debug_check_clauses : bool Config.T
  val debug_prefix_clause_id_with_hash : bool Config.T
  val debug_trace_all_clauses : bool Config.T

  val debug_messages: bool Unsynchronized.ref
  val debug_msg: (unit -> string) -> unit

  val cpu_time_milliseconds : ('a -> 'b) -> 'a -> 'b * int
  val time_and_trace : ((unit -> string) -> unit) -> ('a -> 'b) -> 'a -> 'b

  datatype ('a, 'b) either = Left of 'a | Right of 'b
  val get_left : ('a, 'b) either -> 'a option
  val assert_results_eq : ('a -> ''b) -> ('a -> ''b) -> 'a -> ''b
end

structure Slam_Common : SLAM_COMMON =
struct

(** configuration **)

(* for tracing *)
fun I x = x

(* overrides all other tracing options *)
val trace = Attrib.setup_config_bool \<^binding>\<open>slam_trace\<close> (K false)
fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ();

val trace_active = Attrib.setup_config_bool \<^binding>\<open>slam_trace_active\<close> (K true)
(* FIXME change to int and show only that many *)
val trace_passive = Attrib.setup_config_bool \<^binding>\<open>slam_trace_passive\<close> (K true)

(* override slam_trace during the respective phases *)
val trace_forward_simp = Attrib.setup_config_bool \<^binding>\<open>slam_trace_forward_simp\<close> (K false)
val trace_backward_simp = Attrib.setup_config_bool \<^binding>\<open>slam_trace_backward_simp\<close> (K false)
val trace_cheap_simp = Attrib.setup_config_bool \<^binding>\<open>slam_trace_cheap_simp\<close> (K false)

val trace_archive = Attrib.setup_config_bool \<^binding>\<open>slam_trace_archive\<close> (K false)
val trace_inferred = Attrib.setup_config_bool \<^binding>\<open>slam_trace_inferred\<close> (K false)

(* individual rules *)
val trace_sup = Attrib.setup_config_bool \<^binding>\<open>slam_trace_sup\<close> (K false)
val trace_e_res = Attrib.setup_config_bool \<^binding>\<open>slam_trace_e_res\<close> (K false)
val trace_imitate_project = Attrib.setup_config_bool \<^binding>\<open>slam_trace_imitate_project\<close> (K false)
val trace_e_fact = Attrib.setup_config_bool \<^binding>\<open>slam_trace_e_fact\<close> (K false)
val trace_arg_cong = Attrib.setup_config_bool \<^binding>\<open>slam_trace_arg_cong\<close> (K false)
val trace_bool_hoist = Attrib.setup_config_bool \<^binding>\<open>slam_trace_bool_hoist\<close> (K false)
val trace_false_elim = Attrib.setup_config_bool \<^binding>\<open>slam_trace_false_elim\<close> (K false)
val trace_eq_hoist = Attrib.setup_config_bool \<^binding>\<open>slam_trace_eq_hoist\<close> (K false)
val trace_neq_hoist = Attrib.setup_config_bool \<^binding>\<open>slam_trace_neq_hoist\<close> (K false)
val trace_forall_hoist = Attrib.setup_config_bool \<^binding>\<open>slam_trace_forall_hoist\<close> (K false)
val trace_exists_hoist = Attrib.setup_config_bool \<^binding>\<open>slam_trace_exists_hoist\<close> (K false)
val trace_bool_rw = Attrib.setup_config_bool \<^binding>\<open>slam_trace_bool_rw\<close> (K false)
val trace_forall_rw = Attrib.setup_config_bool \<^binding>\<open>slam_trace_forall_rw\<close> (K false)
val trace_exists_rw = Attrib.setup_config_bool \<^binding>\<open>slam_trace_exists_rw\<close> (K false)
val trace_neg_ext = Attrib.setup_config_bool \<^binding>\<open>slam_trace_neg_ext\<close> (K false)
val trace_neg_cong_fun = Attrib.setup_config_bool \<^binding>\<open>slam_trace_neg_cong_fun\<close> (K false)
val trace_delete_duplicated_lits = Attrib.setup_config_bool \<^binding>\<open>slam_trace_delete_duplicated_lits\<close> (K false)
val trace_delete_resolved_lits = Attrib.setup_config_bool \<^binding>\<open>slam_trace_delete_resolved_lits\<close> (K false)
val trace_destructive_e_res = Attrib.setup_config_bool \<^binding>\<open>slam_trace_destructive_e_res\<close> (K false)
val trace_flex_flex_simp = Attrib.setup_config_bool \<^binding>\<open>slam_trace_flex_flex_simp\<close> (K false)
val trace_rewrite_lits = Attrib.setup_config_bool \<^binding>\<open>slam_trace_rewrite_lits\<close> (K false)
val trace_positive_simplify_reflect = Attrib.setup_config_bool \<^binding>\<open>slam_trace_positive_simplify_reflect\<close> (K false)
val trace_negative_simplify_reflect = Attrib.setup_config_bool \<^binding>\<open>slam_trace_negative_simplify_reflect\<close> (K false)
val trace_simp_outer_claus = Attrib.setup_config_bool \<^binding>\<open>slam_trace_simp_outer_claus\<close> (K false)
val trace_bool_simp = Attrib.setup_config_bool \<^binding>\<open>slam_trace_bool_simp\<close> (K false)
val trace_simp_false_elim = Attrib.setup_config_bool \<^binding>\<open>slam_trace_simp_false_elim\<close> (K false)
val trace_syntactic_tautology_deletion1 = Attrib.setup_config_bool \<^binding>\<open>slam_trace_syntactic_tautology_deletion1\<close> (K false)
val trace_syntactic_tautology_deletion2 = Attrib.setup_config_bool \<^binding>\<open>slam_trace_syntactic_tautology_deletion2\<close> (K false)
val trace_clause_subsumption = Attrib.setup_config_bool \<^binding>\<open>slam_trace_clause_subsumption\<close> (K false)
val trace_equality_subsumption = Attrib.setup_config_bool \<^binding>\<open>slam_trace_equality_subsumption\<close> (K false)

val trace_detailed_origin = Attrib.setup_config_bool \<^binding>\<open>slam_trace_detailed_origin\<close> (K false)

(* FIXME: actually use this config option *)
val report_main_loop_timing = Attrib.setup_config_bool \<^binding>\<open>slam_report_main_loop_timing\<close> (K false)

val trace_rule_timing = Attrib.setup_config_bool \<^binding>\<open>slam_trace_rule_timing\<close> (K false)
val trace_all_rule_timings =
  Attrib.setup_config_bool \<^binding>\<open>slam_trace_all_rule_timings\<close> (K false)

(* only output if trace would *)
fun trace_msg_active ctxt msg = if Config.get ctxt trace_active then trace_msg ctxt msg else ();
fun trace_msg_passive ctxt msg = if Config.get ctxt trace_passive then trace_msg ctxt msg else ();
fun trace_msg_forward_simp ctxt msg =
  if Config.get ctxt trace_forward_simp
    then trace_msg ctxt (fn () => "forward simplification: " ^ msg ())
    else ();
fun trace_msg_backward_simp ctxt msg =
  if Config.get ctxt trace_backward_simp
    then trace_msg ctxt (fn () => "backward simplification: " ^ msg ())
    else ();
fun trace_msg_cheap_simp ctxt msg =
  if Config.get ctxt trace_cheap_simp
    then trace_msg ctxt (fn () => "cheap simplification: " ^ msg ())
    else ();
fun trace_msg_archive ctxt msg = if Config.get ctxt trace_archive then trace_msg ctxt msg else ();
fun trace_msg_inferred ctxt msg = if Config.get ctxt trace_inferred then trace_msg ctxt msg else ();

(* individual rules *)
fun trace_msg_sup ctxt msg = if Config.get ctxt trace_sup then trace_msg ctxt msg else ();
fun trace_msg_e_res ctxt msg = if Config.get ctxt trace_e_res then trace_msg ctxt msg else ();
fun trace_msg_imitate_project ctxt msg = if Config.get ctxt trace_imitate_project then trace_msg ctxt msg else ();
fun trace_msg_e_fact ctxt msg = if Config.get ctxt trace_e_fact then trace_msg ctxt msg else ();
fun trace_msg_arg_cong ctxt msg = if Config.get ctxt trace_arg_cong then trace_msg ctxt msg else ();
fun trace_msg_bool_hoist ctxt msg = if Config.get ctxt trace_bool_hoist then trace_msg ctxt msg else ();
fun trace_msg_false_elim ctxt msg = if Config.get ctxt trace_false_elim then trace_msg ctxt msg else ();
fun trace_msg_eq_hoist ctxt msg = if Config.get ctxt trace_eq_hoist then trace_msg ctxt msg else ();
fun trace_msg_neq_hoist ctxt msg = if Config.get ctxt trace_neq_hoist then trace_msg ctxt msg else ();
fun trace_msg_forall_hoist ctxt msg = if Config.get ctxt trace_forall_hoist then trace_msg ctxt msg else ();
fun trace_msg_exists_hoist ctxt msg = if Config.get ctxt trace_exists_hoist then trace_msg ctxt msg else ();
fun trace_msg_bool_rw ctxt msg = if Config.get ctxt trace_bool_rw then trace_msg ctxt msg else ();
fun trace_msg_forall_rw ctxt msg = if Config.get ctxt trace_forall_rw then trace_msg ctxt msg else ();
fun trace_msg_exists_rw ctxt msg = if Config.get ctxt trace_exists_rw then trace_msg ctxt msg else ();
fun trace_msg_neg_ext ctxt msg = if Config.get ctxt trace_neg_ext then trace_msg ctxt msg else ();
fun trace_msg_neg_cong_fun ctxt msg = if Config.get ctxt trace_neg_cong_fun then trace_msg ctxt msg else ();
fun trace_msg_delete_duplicated_lits ctxt msg = if Config.get ctxt trace_delete_duplicated_lits then trace_msg ctxt msg else ();
fun trace_msg_delete_resolved_lits ctxt msg = if Config.get ctxt trace_delete_resolved_lits then trace_msg ctxt msg else ();
fun trace_msg_destructive_e_res ctxt msg = if Config.get ctxt trace_destructive_e_res then trace_msg ctxt msg else ();
fun trace_msg_flex_flex_simp ctxt msg = if Config.get ctxt trace_flex_flex_simp then trace_msg ctxt msg else ();
fun trace_msg_rewrite_lits ctxt msg = if Config.get ctxt trace_rewrite_lits then trace_msg ctxt msg else ();
fun trace_msg_positive_simplify_reflect ctxt msg = if Config.get ctxt trace_positive_simplify_reflect then trace_msg ctxt msg else ();
fun trace_msg_negative_simplify_reflect ctxt msg = if Config.get ctxt trace_negative_simplify_reflect then trace_msg ctxt msg else ();
fun trace_msg_simp_outer_claus ctxt msg = if Config.get ctxt trace_simp_outer_claus then trace_msg ctxt msg else ();
fun trace_msg_bool_simp ctxt msg = if Config.get ctxt trace_bool_simp then trace_msg ctxt msg else ();
fun trace_msg_simp_false_elim ctxt msg = if Config.get ctxt trace_simp_false_elim then trace_msg ctxt msg else ();
(*
fun trace_msg_syntactic_tautology_deletion1 ctxt msg = if Config.get ctxt trace_syntactic_tautology_deletion1 then trace_msg ctxt msg else ();
fun trace_msg_syntactic_tautology_deletion2 ctxt msg = if Config.get ctxt trace_syntactic_tautology_deletion2 then trace_msg ctxt msg else ();
*)
fun trace_msg_clause_subsumption ctxt msg = if Config.get ctxt trace_clause_subsumption then trace_msg ctxt msg else ();
fun trace_msg_equality_subsumption ctxt msg = if Config.get ctxt trace_equality_subsumption then trace_msg ctxt msg else ();

datatype proof_reconstruction_mode = Cheat | Argo | Metis | Blast | Manual

fun string_of_proof_reconstruction_mode Cheat = "cheat"
  | string_of_proof_reconstruction_mode Argo = "argo"
  | string_of_proof_reconstruction_mode Metis = "metis"
  | string_of_proof_reconstruction_mode Blast = "blast"
  | string_of_proof_reconstruction_mode Manual = "manual"

fun parse_proof_reconstruction_mode "cheat" = Cheat
  | parse_proof_reconstruction_mode "argo" = Argo
  | parse_proof_reconstruction_mode "metis" = Metis
  | parse_proof_reconstruction_mode "blast" = Blast
  | parse_proof_reconstruction_mode "manual" = Manual
  | parse_proof_reconstruction_mode s = error
      ( "Not a valid slam proof reconstruction mode: "
      ^ s
      ^ " (must be either of \"cheat\", \"argo\", \"metis\", \"blast\" or \"manual\")" )

val proof_reconstruction =
  Attrib.setup_config_string
    \<^binding>\<open>slam_proof_reconstruction\<close>
    (K (string_of_proof_reconstruction_mode Cheat))
(* val proof_reconstruction = Attrib.setup_config_bool \<^binding>\<open>slam_proof_reconstruction\<close> (K true) *)

fun get_proof_reconstruction_mode ctxt = parse_proof_reconstruction_mode (Config.get ctxt proof_reconstruction)

val max_number_of_steps = Attrib.setup_config_int \<^binding>\<open>slam_max_number_of_steps\<close> (K 2000)

(* smart options *)

type smart_value = bool option

val smartN = "smart"
val onN = "on"
val offN = "off"

fun string_of_smart_value smart_value = case smart_value of
    NONE => smartN
  | SOME b => if b then onN else offN

fun parse_smart_value s = case s of
    "smart" => NONE
  | "on" => SOME true
  | "off" => SOME false
  | _ => error ("parse_smart: invalid string value \"" ^ s ^ "\"")

fun get_smart ctxt cfg =
  let
    val value = Config.get ctxt cfg
  in
    if value = onN
      then SOME true
    else if value = offN
      then SOME false
    else if value = smartN
      then NONE
    else
      error ("get_smart: invalid value for smart option " ^ Config.name_of cfg ^ "=\"" ^ Config.get ctxt cfg)
  end

fun get_smart_default ctxt cfg = the_default true (get_smart ctxt cfg)

fun put_smart (cfg, enable) ctxt =
  let
    val new_value = if enable then onN else offN
  in
    if Config.get ctxt cfg = smartN
      then Config.put cfg new_value ctxt
      else
        (warning ("Leaving preset value " ^ Config.name_of cfg ^ "=\"" ^ Config.get ctxt cfg ^
          "\" instead of setting to \"" ^ new_value ^ "\"");
        ctxt)
  end

val put_smarts = fold put_smart

(* Disable all rules that are set to "smart". *)
val disable_all = Attrib.setup_config_bool \<^binding>\<open>slam_disable_all\<close> (K false)

(* inferences *)
val rule_sup = Attrib.setup_config_string \<^binding>\<open>slam_rule_sup\<close> (K smartN)
val rule_fluid_sup = Attrib.setup_config_string \<^binding>\<open>slam_rule_fluid_sup\<close> (K smartN)
val rule_e_res = Attrib.setup_config_string \<^binding>\<open>slam_rule_e_res\<close> (K smartN)
val rule_imitate_project = Attrib.setup_config_string \<^binding>\<open>slam_rule_imitate_project\<close> (K smartN)
val rule_e_fact = Attrib.setup_config_string \<^binding>\<open>slam_rule_e_fact\<close> (K smartN)
val rule_arg_cong = Attrib.setup_config_string \<^binding>\<open>slam_rule_arg_cong\<close> (K smartN)
val rule_bool_hoist = Attrib.setup_config_string \<^binding>\<open>slam_rule_bool_hoist\<close> (K smartN)
val rule_false_elim = Attrib.setup_config_string \<^binding>\<open>slam_rule_false_elim\<close> (K smartN)
val rule_eq_hoist = Attrib.setup_config_string \<^binding>\<open>slam_rule_eq_hoist\<close> (K smartN)
val rule_neq_hoist = Attrib.setup_config_string \<^binding>\<open>slam_rule_neq_hoist\<close> (K smartN)
val rule_forall_hoist = Attrib.setup_config_string \<^binding>\<open>slam_rule_forall_hoist\<close> (K smartN)
val rule_exists_hoist = Attrib.setup_config_string \<^binding>\<open>slam_rule_exists_hoist\<close> (K smartN)
val rule_bool_rw = Attrib.setup_config_string \<^binding>\<open>slam_rule_bool_rw\<close> (K smartN)
val rule_forall_rw = Attrib.setup_config_string \<^binding>\<open>slam_rule_forall_rw\<close> (K smartN)
val rule_exists_rw = Attrib.setup_config_string \<^binding>\<open>slam_rule_exists_rw\<close> (K smartN)
val rule_fluid_bool_hoist = Attrib.setup_config_string \<^binding>\<open>slam_rule_fluid_bool_hoist\<close> (K smartN)
val rule_fluid_loob_hoist = Attrib.setup_config_string \<^binding>\<open>slam_rule_fluid_loob_hoist\<close> (K smartN)
val rule_ext = Attrib.setup_config_string \<^binding>\<open>slam_rule_ext\<close> (K smartN)
val rule_neg_ext = Attrib.setup_config_string \<^binding>\<open>slam_rule_neg_ext\<close> (K smartN)
val rule_neg_cong_fun = Attrib.setup_config_string \<^binding>\<open>slam_rule_neg_cong_fun\<close> (K smartN)
val rule_choice = Attrib.setup_config_string \<^binding>\<open>slam_rule_choice\<close> (K smartN)
(* simplifications *)
val rule_delete_duplicated_lits = Attrib.setup_config_string \<^binding>\<open>slam_rule_delete_duplicated_lits\<close> (K smartN)
val rule_delete_resolved_lits = Attrib.setup_config_string \<^binding>\<open>slam_rule_delete_resolved_lits\<close> (K smartN)
val rule_destructive_e_res = Attrib.setup_config_string \<^binding>\<open>slam_rule_destructive_e_res\<close> (K smartN)
val rule_flex_flex_simp = Attrib.setup_config_string \<^binding>\<open>slam_rule_flex_flex_simp\<close> (K smartN)
val rule_rewrite_lits = Attrib.setup_config_string \<^binding>\<open>slam_rule_rewrite_lits\<close> (K smartN)
val rule_positive_simplify_reflect = Attrib.setup_config_string \<^binding>\<open>slam_rule_positive_simplify_reflect\<close> (K smartN)
val rule_negative_simplify_reflect = Attrib.setup_config_string \<^binding>\<open>slam_rule_negative_simplify_reflect\<close> (K smartN)
val rule_simp_outer_claus = Attrib.setup_config_string \<^binding>\<open>slam_rule_simp_outer_claus\<close> (K smartN)
val rule_bool_simp = Attrib.setup_config_string \<^binding>\<open>slam_rule_bool_simp\<close> (K smartN)
val rule_simp_false_elim = Attrib.setup_config_string \<^binding>\<open>slam_rule_simp_false_elim\<close> (K smartN)
val rule_syntactic_tautology_deletion1 = Attrib.setup_config_string \<^binding>\<open>slam_rule_syntactic_tautology_deletion1\<close> (K smartN)
val rule_syntactic_tautology_deletion2 = Attrib.setup_config_string \<^binding>\<open>slam_rule_syntactic_tautology_deletion2\<close> (K smartN)
val rule_clause_subsumption = Attrib.setup_config_string \<^binding>\<open>slam_rule_clause_subsumption\<close> (K smartN)
val rule_equality_subsumption = Attrib.setup_config_string \<^binding>\<open>slam_rule_equality_subsumption\<close> (K smartN)

val rule_enabled = get_smart_default

(* rule sets *)

val all_rules =
  [ rule_sup
  , rule_fluid_sup
  , rule_e_res
  , rule_imitate_project
  , rule_e_fact
  , rule_arg_cong
  , rule_bool_hoist
  , rule_false_elim
  , rule_eq_hoist
  , rule_neq_hoist
  , rule_forall_hoist
  , rule_exists_hoist
  , rule_bool_rw
  , rule_forall_rw
  , rule_exists_rw
  , rule_fluid_bool_hoist
  , rule_fluid_loob_hoist
  , rule_ext
  , rule_neg_ext
  , rule_neg_cong_fun
  , rule_choice
  , rule_delete_duplicated_lits
  , rule_delete_resolved_lits
  , rule_destructive_e_res
  , rule_flex_flex_simp
  , rule_rewrite_lits
  , rule_positive_simplify_reflect
  , rule_negative_simplify_reflect
  , rule_simp_outer_claus
  , rule_bool_simp
  , rule_simp_false_elim
  , rule_syntactic_tautology_deletion1
  , rule_syntactic_tautology_deletion2
  , rule_clause_subsumption
  , rule_equality_subsumption
  ]

val first_order_core_rules = [rule_sup, rule_e_res, rule_e_fact]

val higher_order_core_rules = [rule_arg_cong]

val ext_rules = [rule_neg_ext]

val fluid_rules = [rule_fluid_sup, rule_fluid_bool_hoist]

val boolean_rules =
  [ rule_bool_hoist
  , rule_false_elim
  , rule_eq_hoist
  , rule_neq_hoist
  , rule_forall_hoist
  , rule_exists_hoist
  , rule_bool_rw
  , rule_forall_rw
  , rule_exists_rw
  , rule_simp_outer_claus
  , rule_simp_false_elim
  , rule_bool_simp
  ]

val simp_rules =
  [ rule_delete_duplicated_lits
  , rule_delete_resolved_lits
  , rule_flex_flex_simp
  , rule_positive_simplify_reflect
  , rule_negative_simplify_reflect
  , rule_simp_outer_claus
  , rule_bool_simp
  , rule_simp_false_elim
  , rule_syntactic_tautology_deletion1
  , rule_syntactic_tautology_deletion2
  , rule_clause_subsumption
  , rule_equality_subsumption
  ]

(* doesn't really make sense to turn these off *)
val cheap_rules =
  [ rule_delete_duplicated_lits
  , rule_delete_resolved_lits
  , rule_flex_flex_simp
  , rule_simp_false_elim
  , rule_bool_simp
  , rule_syntactic_tautology_deletion1
  , rule_syntactic_tautology_deletion2
  ]

val delayed_unification = Attrib.setup_config_string \<^binding>\<open>slam_delayed_unification\<close> (K smartN)
val delayed_unification_simpl_only = Attrib.setup_config_string \<^binding>\<open>slam_delayed_unification_simpl_only\<close> (K smartN)

datatype ho_unification_strategy
  = SmashFlexFlex
  | DelayFlexFlex
  | SimplOnly (* similar to Vampire's depth zero + Imitate + Project *)

val ho_unification_strategies = [SmashFlexFlex, DelayFlexFlex, SimplOnly]

fun config_value_set_of_ho_unification_strategy strat = case strat of
    SmashFlexFlex =>
      [(delayed_unification, false), (delayed_unification_simpl_only, false), (rule_imitate_project, false)]
  | DelayFlexFlex =>
      [(delayed_unification, true), (delayed_unification_simpl_only, false), (rule_imitate_project, false)]
  | SimplOnly =>
      [(delayed_unification, true), (delayed_unification_simpl_only, true), (rule_imitate_project, true)]

fun string_of_ho_unification_strategy strat = case strat of
    SmashFlexFlex => "smash_flex_flex"
  | DelayFlexFlex => "delay_flex_flex"
  | SimplOnly => "simpl_only"

val clause_selection_heuristic_choices =
  map (quote o string_of_ho_unification_strategy) ho_unification_strategies
  |> space_implode ", "

fun parse_ho_unification_strategy s = case s of
    "smash_flex_flex" => SmashFlexFlex
  | "delay_flex_flex" => DelayFlexFlex
  | "simpl_only" => SimplOnly
  | _ => error
      ( "Not a valid higher-order unification strategy: "
      ^ s
      ^ " (must be either of " ^ clause_selection_heuristic_choices ^ ")")

val ho_unification_strategy = Attrib.setup_config_string \<^binding>\<open>slam_ho_unification_strategy\<close> (K (string_of_ho_unification_strategy SmashFlexFlex))

fun get_ho_unification_strategy ctxt =
  parse_ho_unification_strategy (Config.get ctxt ho_unification_strategy)

val unifier_cutoff = Attrib.setup_config_int \<^binding>\<open>slam_unifier_cutoff\<close> (K 2)
fun get_unifier_cutoff ctxt = Config.get ctxt unifier_cutoff

datatype clause_selection_heuristic = Default | DelayedSimpOnlyUnification

val clause_selection_heuristics = [Default, DelayedSimpOnlyUnification]

fun string_of_clause_selection_heuristic Default = "default"
  | string_of_clause_selection_heuristic DelayedSimpOnlyUnification = "delayed_simp_only_unification"

val clause_selection_heuristic = Attrib.setup_config_string \<^binding>\<open>slam_clause_selection_heuristic\<close> (K (string_of_clause_selection_heuristic Default))

val clause_selection_heuristic_choices =
  map (quote o string_of_clause_selection_heuristic) clause_selection_heuristics
  |> space_implode ", "

fun parse_clause_selection_heuristic "default" = Default
  | parse_clause_selection_heuristic "delayed_simp_only_unification" = DelayedSimpOnlyUnification
  | parse_clause_selection_heuristic s = error
      ( "Not a valid clause selection heuristic: "
      ^ s
      ^ " (must be either of " ^ clause_selection_heuristic_choices ^ ")")

fun get_clause_selection_heuristic ctxt =
  parse_clause_selection_heuristic (Config.get ctxt clause_selection_heuristic)

(* number of extra conclusions generated by ArgCong if the return type of s is a type variable *)
val arg_cong_extra_conclusions = Attrib.setup_config_int \<^binding>\<open>slam_arg_cong_extra_conclusions\<close> (K 0)
fun get_arg_cong_extra_conclusions ctxt = Config.get ctxt arg_cong_extra_conclusions

val select_negativoid = Attrib.setup_config_bool \<^binding>\<open>slam_select_negativoid\<close> (K true)
val select_flex_sided = Attrib.setup_config_bool \<^binding>\<open>slam_select_flex_sided\<close> (K false)
val literal_selection_function = Attrib.setup_config_string \<^binding>\<open>slam_literal_selection_function\<close> (K "select_first_neg_lit")

val restricted_destructive_e_res = Attrib.setup_config_bool \<^binding>\<open>slam_restricted_destructive_e_res\<close> (K true)

datatype sup_variable_condition = None | FirstOrder | Approximate

val sup_variable_conditions = [None, FirstOrder, Approximate]

fun string_of_sup_variable_condition None = "none"
  | string_of_sup_variable_condition FirstOrder = "first_order"
  | string_of_sup_variable_condition Approximate = "approximate"

val sup_variable_condition_choices =
  map (quote o string_of_sup_variable_condition) sup_variable_conditions
  |> space_implode ", "

fun parse_sup_variable_condition "none" = None
  | parse_sup_variable_condition "first_order" = FirstOrder
  | parse_sup_variable_condition "approximate" = Approximate
  | parse_sup_variable_condition s = error
      ( "Not a valid slam superposition vairable condition: "
      ^ s
      ^ " (must be either of " ^ sup_variable_condition_choices ^ ")")

val sup_variable_condition = Attrib.setup_config_string \<^binding>\<open>slam_sup_variable_condition\<close> (K (string_of_sup_variable_condition FirstOrder))

fun get_sup_variable_condition ctxt =
  parse_sup_variable_condition (Config.get ctxt sup_variable_condition)

(* FIXME: unnecessary now that we have SIMPL-only delayed unification? *)
val neg_cong_fun_reveal_variable_headed = Attrib.setup_config_bool \<^binding>\<open>slam_neg_cong_fun_reveal_variable_headed\<close> (K true)

(* FIXME: split into sup_into_var_headed, ... *)
val sup_into_fluid = Attrib.setup_config_bool \<^binding>\<open>slam_sup_into_fluid\<close> (K true)

val sup_into_deeply_occuring = Attrib.setup_config_bool \<^binding>\<open>slam_sup_into_deeply_occuring\<close> (K true)

val sup_into_non_eligible = Attrib.setup_config_bool \<^binding>\<open>slam_sup_into_non_eligible\<close> (K false)
val sup_from_non_eligible = Attrib.setup_config_bool \<^binding>\<open>slam_sup_from_non_eligible\<close> (K false)

val bool_simp_quantifiers = Attrib.setup_config_bool \<^binding>\<open>slam_bool_simp_quantifiers\<close> (K true)
val bool_simp_if_then_else = Attrib.setup_config_bool \<^binding>\<open>slam_bool_simp_if_then_else\<close> (K true)

val forward_rewrite_countdown = Attrib.setup_config_int \<^binding>\<open>slam_forward_rewrite_countdown\<close> (K 10)

(* Note: disables ArgCong as an inference *)
val arg_cong_as_simpl = Attrib.setup_config_bool \<^binding>\<open>slam_arg_cong_as_simpl\<close> (K false)

(* Note: disables NegExt as an inference *)
val neg_ext_as_simpl = Attrib.setup_config_bool \<^binding>\<open>slam_neg_ext_as_simpl\<close> (K false)

(* Unfold bounded forall, if-else, etc. *)
val presimplify = Attrib.setup_config_bool \<^binding>\<open>slam_presimplify\<close> (K true)

val meson = Attrib.setup_config_bool \<^binding>\<open>slam_meson\<close> (K false)

fun init_config ctxt =
  ctxt
  |> (put_smarts (config_value_set_of_ho_unification_strategy (get_ho_unification_strategy ctxt)))
  |> (if Config.get ctxt disable_all then fold (fn rule => put_smart (rule, false)) all_rules else I)

fun validate_max_number_of_steps ctxt =
  let
    val value = Config.get ctxt max_number_of_steps
  in
    if value >= 0
      then ()
    else if value = ~1
      then warning "no heartbeat (slam_max_number_of_steps set to -1)"
    else
      error ("validate_max_number_of_steps: Invalid slam_max_number_of_steps: must be \<ge> -1.")
  end

fun validate_delayed_unification ctxt =
  if (get_smart_default ctxt delayed_unification_simpl_only andalso
        not (get_smart_default ctxt delayed_unification)) then
    warning "slam_delayed_unification_simpl_only has no effect without slam_delayed_unification"
  else
    ()

fun validate_smart ctxt cfg =
  let
    val _: smart_value =
      parse_smart_value (Config.get ctxt cfg)
      handle ERROR msg => error ("validate_smart: " ^ Config.name_of cfg ^ ": " ^ msg)
  in
    ()
  end

fun validate_all_rule_values ctxt = (map (validate_smart ctxt) all_rules; ())

fun validate_config ctxt =
  let
    val _: proof_reconstruction_mode = get_proof_reconstruction_mode ctxt
    val _: sup_variable_condition = get_sup_variable_condition ctxt
    val _: unit = validate_max_number_of_steps ctxt
    val _: unit = validate_delayed_unification ctxt
    val _: clause_selection_heuristic = get_clause_selection_heuristic ctxt
    val _: unit = validate_all_rule_values ctxt
    val _: ho_unification_strategy = get_ho_unification_strategy ctxt
  in
    ()
  end

val unify_search_bound = Attrib.setup_config_int \<^binding>\<open>slam_unify_search_bound\<close> (K 200)
val unify_timeout_ms = Attrib.setup_config_int \<^binding>\<open>slam_unify_timeout_ms\<close> (K 0)
val unify_matchcopy_fuel = Attrib.setup_config_int \<^binding>\<open>slam_unify_matchcopy_fuel\<close> (K 50);
val supress_unify_trace = Attrib.setup_config_bool \<^binding>\<open>slam_supress_unify_trace\<close> (K true)

val debug_check_clauses = Attrib.setup_config_bool \<^binding>\<open>slam_debug_check_clauses\<close> (K false)
val debug_prefix_clause_id_with_hash = Attrib.setup_config_bool \<^binding>\<open>slam_debug_prefix_clause_id_with_hash\<close> (K false)
val debug_trace_all_clauses = Attrib.setup_config_bool \<^binding>\<open>slam_debug_trace_all_clauses\<close> (K false)

(** term parsing antiquotations **)

(* From the cookbook. Use

setup \<open> Slam_Common.term_pat_setup \<close>

setup \<open> Slam_Common.type_pat_setup \<close>

in .thy files.

NOTE: @{term_pat "c :: 'a} gives type ?'a instead of 'a, see term_schem below *)
val term_pat_setup =
let
  val parser = Args.context -- Scan.lift Parse.embedded_inner_syntax

  fun term_pat (ctxt, str) =
    str |> Proof_Context.read_term_pattern ctxt |> ML_Syntax.print_term |> ML_Syntax.atomic
in
  ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat)
end

val type_pat_setup =
let
  val parser = Args.context -- Scan.lift Parse.embedded_inner_syntax

  fun typ_pat (ctxt, str) =
    let
      val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    in
      str |> Syntax.read_typ ctxt' |> ML_Syntax.print_typ |> ML_Syntax.atomic
    end
in
  ML_Antiquotation.inline @{binding "typ_pat"} (parser >> typ_pat)
end

(* See
https://isabelle.zulipchat.com/#narrow/stream/336180-Archive-Mirror.3A-Isabelle-Users-Mailing-List/topic/.5Bisabelle.5D.20Work.20on.20a.20new.20theorem.20prover/near/294329598

  "The @{term_pat} antiqutation is a bit strange. If you really mean to
  refer to schematic terms, you should say so via
  Proof_Context.mode_schematic, and not Proof_Context.mode_pattern."

Use

setup \<open> Slam_Common.term_schem_setup \<close>

in .thy files. *)
val term_schem_setup =
let
  val parser = Args.context -- Scan.lift Parse.embedded_inner_syntax

  fun term_schem (ctxt, str) =
    str |> Proof_Context.read_term_schematic ctxt |> ML_Syntax.print_term |> ML_Syntax.atomic
in
  ML_Antiquotation.inline @{binding "term_schem"} (parser >> term_schem)
end

(** pretty / unpretty printing **)

(* much from cookboock *)
fun verbose_of ctxt = config_put_many_bool ctxt
  [show_types, show_markup, show_sorts, show_structs]
and config_put_many_bool ctxt options =
  List.foldr (fn (option, ctxt) => Config.put option true ctxt) ctxt options

fun pretty_term' ctxt t = Syntax.pretty_term ctxt t
val pretty_term = Pretty.string_of oo pretty_term'

fun pretty_typ' ctxt T = Syntax.pretty_typ ctxt T
val pretty_typ = Pretty.string_of oo pretty_typ'

fun pretty_terms' ctxt terms =
  terms
  |> map (Syntax.pretty_term ctxt)
  |> Pretty.commas |> Pretty.block
val pretty_terms = Pretty.string_of oo pretty_terms'

fun pretty_helper aux env = env
  |> Vartab.dest
  |> map aux
  |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
  |> Pretty.enum "," "[" "]"

fun pretty_tyenv' ctxt tyenv =
let
  fun get_typs (v, (s, T)) = (TVar (v, s), T)
  val print = apply2 (Syntax.pretty_typ ctxt)
in
  pretty_helper (print o get_typs) tyenv
end

val pretty_tyenv = Pretty.string_of oo pretty_tyenv'

fun pretty_tenv' ctxt tenv =
let
  fun get_trms (v, (T, t)) = (Var (v, T), t)
  val print = apply2 (Syntax.pretty_term ctxt)
in
  pretty_helper (print o get_trms) tenv
end;

val pretty_tenv = Pretty.string_of oo pretty_tenv'

fun label_pretty name pretty = Pretty.block ([Pretty.str (name ^ "="), pretty])

fun pretty_env' ctxt env =
  Pretty.block (
    [ label_pretty "ty" (pretty_tyenv' ctxt (Envir.type_env env))
    , Pretty.brk 1
    , label_pretty "tm" (pretty_tenv' ctxt (Envir.term_env env))
    ]
  )

val pretty_env = Pretty.string_of oo pretty_env'

fun pretty_preunifier' ctxt (env, flex_flex_pairs) =
  Pretty.block
    [ pretty_env' ctxt env
    , Pretty.brk 1
    (* from pretty_thm_raw from more_thm.ML *)
    , label_pretty "ff" (Pretty.list "[" "]" (map (Pretty.block o Syntax.pretty_flexpair ctxt) flex_flex_pairs))
    ]

val pretty_preunifier = Pretty.string_of oo pretty_preunifier'

(* from the cookbook
(* switch to unpretty printer *)
ML_system_pp (fn _ => fn _ => Pretty.to_polyml o Slam_Common.raw_pp_typ);
ML_system_pp (fn _ => fn _ => Pretty.to_polyml o Slam_Common.raw_pp_term);
(* reset to default pretty printer *)
ML_system_pp (fn depth => fn _ => ML_Pretty.to_polyml o Pretty.to_ML depth o Proof_Display.pp_typ Theory.get_pure);
ML_system_pp (fn depth => fn _ => ML_Pretty.to_polyml o Pretty.to_ML depth o Proof_Display.pp_term Theory.get_pure);
*)
local
  fun pp_pair (x, y) = Pretty.list "(" ")" [x, y]
  fun pp_triple (x, y, z) = Pretty.list "(" ")" [x, y, z]
  fun pp_list xs = Pretty.list "[" "]" xs
  fun pp_str s = Pretty.str s
  fun pp_qstr s = Pretty.quote (pp_str s)
  fun pp_int i = pp_str (string_of_int i)
  fun pp_sort S = pp_list (map pp_qstr S)
  fun pp_constr a args = Pretty.block [pp_str a, Pretty.brk 1, args]
in
fun raw_pp_typ (TVar ((a, i), S)) = pp_constr "TVar" (pp_pair (pp_pair (pp_qstr a, pp_int i), pp_sort S))
| raw_pp_typ (TFree (a, S)) = pp_constr "TFree" (pp_pair (pp_qstr a, pp_sort S))
| raw_pp_typ (Type (a, tys)) =  pp_constr "Type" (pp_pair (pp_qstr a, pp_list (map raw_pp_typ tys)))
fun raw_pp_term  (Const (c, T)) = pp_constr "Const" (pp_pair (pp_qstr c, raw_pp_typ T))
  | raw_pp_term (Free (x, T)) = pp_constr "Free" (pp_pair (pp_qstr x, raw_pp_typ T))
  | raw_pp_term (Var ((x, i), T)) = pp_constr "Var" (pp_pair (pp_pair (pp_qstr x, pp_int i), raw_pp_typ T))
  | raw_pp_term (Bound i) = pp_constr "Bound" (pp_int i)
  | raw_pp_term (Abs(x, T, t)) = pp_constr "Abs" (pp_triple (pp_qstr x, raw_pp_typ T, raw_pp_term t))
  | raw_pp_term (s $ t) = pp_constr "$" (pp_pair (raw_pp_term s, raw_pp_term t))
end;

(** common utilities **)

val debug_messages = Unsynchronized.ref false
fun debug_msg msg = if !debug_messages then writeln (msg ()) else ()

(* from HOL/Tools/Mirabelle/mirabelle.ML *)
fun cpu_time_milliseconds f x =
  (* CPU time is problematics with multithreading as it refers to the per-process CPU time. *)
  let val ({elapsed, ...}, y) = Timing.timing f x
  in (y, Time.toMilliseconds elapsed) end;

fun time_and_trace channel f x =
  let
    val (res, elapsed) = cpu_time_milliseconds f x
    val () = channel (fn () => "elapsed: " ^ @{make_string} elapsed ^ " ms")
  in
    res
  end

fun time_rule ctxt trace_rule f x =
  if Config.get ctxt trace_all_rule_timings
      orelse (Config.get ctxt trace_rule andalso Config.get ctxt trace_rule_timing)
    then
      time_and_trace
        (trace_msg ctxt o (fn msg => fn () =>
          let
            val name = Config.name_of trace_rule
          in
            \<^assert> (String.isPrefix "slam_trace_" name);
            String.extract (name, 11, NONE) ^ " " ^ msg ()
          end
        ))
        f
        x
    else
      f x

fun map_some _ NONE = NONE
  | map_some f (SOME x) = SOME (f x)

fun some_is p NONE = false
  | some_is p (SOME x) = p x

fun seq_cartesian_product xs ys =
  case Seq.pull xs of
    SOME (x, xs) => Seq.append (Seq.map (pair x) ys) (seq_cartesian_product xs ys)
  | NONE => Seq.empty
  (* Seq.make (fn () =>
    case Seq.pull xs of
      SOME (x, xs) => Seq.pull (Seq.append (Seq.map (pair x) ys) (seq_cartesian_product xs ys))
    | NONE => NONE
  ) *)

fun cartesian_product [] _ = []
  | cartesian_product (x :: xs) ys = map (pair x) ys @ cartesian_product xs ys

datatype ('a, 'b) either = Left of 'a | Right of 'b

fun get_left (Left x) = SOME x
  | get_left (Right _) = NONE

(* Test that two functions give the same result and return that value. *)
fun assert_results_eq g f x =
  let
    val y = f x
  in
    if y = g x
      then y
    else
      error "assert_results_eq: not equal"
  end

end
