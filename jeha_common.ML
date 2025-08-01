
signature JEHA_COMMON =
sig
  (* overrides all other tracing settings *)
  val trace : bool Config.T
  (* output the active set whenver it changes *)
  val trace_active : bool Config.T
  (* output 10 passive clauses at each step *)
  val trace_passive : bool Config.T

  (* override jeha_trace during the respective phases *)
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
  val trace_delete_duplicated_lits : bool Config.T
  val trace_delete_resolved_lits : bool Config.T
  val trace_rewrite_positive_lits : bool Config.T
  val trace_rewrite_negative_lits : bool Config.T
  val trace_positive_simplify_reflect : bool Config.T
  val trace_negative_simplify_reflect : bool Config.T
  val trace_simp_outer_claus : bool Config.T
  val trace_simp_bool_rw : bool Config.T
  val trace_simp_false_elim : bool Config.T
  val trace_syntactic_tautology_deletion1 : bool Config.T
  val trace_syntactic_tautology_deletion2 : bool Config.T
  val trace_clause_subsumption : bool Config.T
  val trace_equality_subsumption : bool Config.T

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
  val trace_msg_delete_duplicated_lits : Proof.context -> (unit -> string) -> unit
  val trace_msg_delete_resolved_lits : Proof.context -> (unit -> string) -> unit
  val trace_msg_rewrite_positive_lits : Proof.context -> (unit -> string) -> unit
  val trace_msg_rewrite_negative_lits : Proof.context -> (unit -> string) -> unit
  val trace_msg_positive_simplify_reflect : Proof.context -> (unit -> string) -> unit
  val trace_msg_negative_simplify_reflect : Proof.context -> (unit -> string) -> unit
  val trace_msg_simp_outer_claus : Proof.context -> (unit -> string) -> unit
  val trace_msg_simp_bool_rw : Proof.context -> (unit -> string) -> unit
  val trace_msg_simp_false_elim : Proof.context -> (unit -> string) -> unit
  (*
  val trace_msg_syntactic_tautology_deletion1 : Proof.context -> (unit -> string) -> unit
  val trace_msg_syntactic_tautology_deletion2 : Proof.context -> (unit -> string) -> unit
  *)
  val trace_msg_clause_subsumption : Proof.context -> (unit -> string) -> unit
  val trace_msg_equality_subsumption : Proof.context -> (unit -> string) -> unit

  val proof_reconstruction : string Config.T
  datatype proof_reconstruction_mode = Cheat | Argo | Metis | Blast | Manual
  val get_proof_reconstruction_mode : Proof.context -> proof_reconstruction_mode

  val term_pat_setup : theory -> theory
  val type_pat_setup : theory -> theory
  val term_schem_setup : theory -> theory
  val verbose_of : Proof.context -> Proof.context
  val pretty_term : Proof.context -> term -> string
  val pretty_term' : Proof.context -> term -> Pretty.T
  val pretty_typ : Proof.context -> typ -> string
  val pretty_terms : Proof.context -> term list -> string
  val pretty_tyenv : Proof.context -> Type.tyenv -> string
  val pretty_tenv : Proof.context -> Envir.tenv -> string
  val raw_pp_typ : typ -> Pretty.T
  val raw_pp_term : term -> Pretty.T
  val I : 'a -> 'a
  val map_some : ('a -> 'b) -> 'a option -> 'b option
  val some_is : ('a -> bool) -> 'a option -> bool
  val seq_cartesian_product : 'a Seq.seq -> 'b Seq.seq -> ('a * 'b) Seq.seq
  val cartesian_product : 'a list -> 'b list -> ('a * 'b) list
  val max_number_of_steps : int Config.T
  (* Config options to turn rules on and off. *)
  val disable_all : bool Config.T
  (* inferences *)
  val rule_sup : bool Config.T
  val rule_fluid_sup : bool Config.T
  val rule_e_res : bool Config.T
  val rule_e_fact : bool Config.T
  val rule_arg_cong : bool Config.T
  val rule_bool_hoist : bool Config.T
  val rule_false_elim : bool Config.T
  val rule_eq_hoist : bool Config.T
  val rule_neq_hoist : bool Config.T
  val rule_forall_hoist : bool Config.T
  val rule_exists_hoist : bool Config.T
  val rule_bool_rw : bool Config.T
  val rule_forall_rw : bool Config.T
  val rule_exists_rw : bool Config.T
  val rule_fluid_bool_hoist : bool Config.T
  val rule_fluid_loob_ho : bool Config.T
  val rule_ext : bool Config.T
  val rule_neg_ext : bool Config.T
  val rule_choice : bool Config.T
  (* simplifications *)
  val rule_delete_duplicated_lits : bool Config.T
  val rule_delete_resolved_lits : bool Config.T
  val rule_rewrite_positive_lits : bool Config.T
  val rule_rewrite_negative_lits : bool Config.T
  val rule_positive_simplify_reflect : bool Config.T
  val rule_negative_simplify_reflect : bool Config.T
  val rule_simp_outer_claus : bool Config.T
  val rule_simp_bool_rw : bool Config.T
  val rule_simp_false_elim : bool Config.T
  val rule_syntactic_tautology_deletion1 : bool Config.T
  val rule_syntactic_tautology_deletion2 : bool Config.T
  val rule_clause_subsumption : bool Config.T
  val rule_equality_subsumption : bool Config.T

  val select_negativoid : bool Config.T
  val select_flex_sided : bool Config.T
  val literal_selection_function : string Config.T

  val unify_search_bound : int Config.T
  val unify_timeout_ms : int Config.T
  val supress_unify_trace : bool Config.T

  val debug_check_clauses : bool Config.T

  val cpu_time_milliseconds : ('a -> 'b) -> 'a -> 'b * int
  val time_and_trace : ((unit -> string) -> unit) -> ('a -> 'b) -> 'a -> 'b

  datatype ('a, 'b) either = Left of 'a | Right of 'b
  val get_left : ('a, 'b) either -> 'a option
  val assert_results_eq : ('a -> ''b) -> ('a -> ''b) -> 'a -> ''b
end

structure Jeha_Common : JEHA_COMMON =
struct

(** configuration **)

(* for tracing *)
fun I x = x

(* overrides all other tracing options *)
val trace = Attrib.setup_config_bool \<^binding>\<open>jeha_trace\<close> (K false)
fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ();

val trace_active = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_active\<close> (K true)
(* FIXME change to int and show only that many *)
val trace_passive = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_passive\<close> (K true)

(* override jeha_trace during the respective phases *)
val trace_forward_simp = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_forward_simp\<close> (K true)
val trace_backward_simp = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_backward_simp\<close> (K false)
val trace_cheap_simp = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_cheap_simp\<close> (K false)

val trace_archive = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_archive\<close> (K false)
val trace_inferred = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_inferred\<close> (K false)

(* individual rules *)
val trace_sup = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_sup\<close> (K false)
val trace_e_res = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_e_res\<close> (K false)
val trace_e_fact = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_e_fact\<close> (K false)
val trace_arg_cong = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_arg_cong\<close> (K false)
val trace_bool_hoist = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_bool_hoist\<close> (K false)
val trace_false_elim = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_false_elim\<close> (K false)
val trace_eq_hoist = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_eq_hoist\<close> (K false)
val trace_neq_hoist = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_neq_hoist\<close> (K false)
val trace_forall_hoist = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_forall_hoist\<close> (K false)
val trace_exists_hoist = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_exists_hoist\<close> (K false)
val trace_bool_rw = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_bool_rw\<close> (K false)
val trace_forall_rw = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_forall_rw\<close> (K false)
val trace_exists_rw = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_exists_rw\<close> (K false)
val trace_neg_ext = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_neg_ext\<close> (K false)
val trace_delete_duplicated_lits = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_delete_duplicated_lits\<close> (K false)
val trace_delete_resolved_lits = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_delete_resolved_lits\<close> (K false)
val trace_rewrite_positive_lits = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_rewrite_positive_lits\<close> (K false)
val trace_rewrite_negative_lits = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_rewrite_negative_lits\<close> (K false)
val trace_positive_simplify_reflect = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_positive_simplify_reflect\<close> (K false)
val trace_negative_simplify_reflect = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_negative_simplify_reflect\<close> (K false)
val trace_simp_outer_claus = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_simp_outer_claus\<close> (K false)
val trace_simp_bool_rw = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_simp_bool_rw\<close> (K false)
val trace_simp_false_elim = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_simp_false_elim\<close> (K false)
val trace_syntactic_tautology_deletion1 = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_syntactic_tautology_deletion1\<close> (K false)
val trace_syntactic_tautology_deletion2 = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_syntactic_tautology_deletion2\<close> (K false)
val trace_clause_subsumption = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_clause_subsumption\<close> (K false)
val trace_equality_subsumption = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_equality_subsumption\<close> (K false)

(* FIXME: actually use this config option *)
val report_main_loop_timing = Attrib.setup_config_bool \<^binding>\<open>jeha_report_main_loop_timing\<close> (K false)

val trace_rule_timing = Attrib.setup_config_bool \<^binding>\<open>jeha_trace_rule_timing\<close> (K false)
val trace_all_rule_timings =
  Attrib.setup_config_bool \<^binding>\<open>jeha_trace_all_rule_timings\<close> (K false)

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
fun trace_msg_delete_duplicated_lits ctxt msg = if Config.get ctxt trace_delete_duplicated_lits then trace_msg ctxt msg else ();
fun trace_msg_delete_resolved_lits ctxt msg = if Config.get ctxt trace_delete_resolved_lits then trace_msg ctxt msg else ();
fun trace_msg_rewrite_positive_lits ctxt msg = if Config.get ctxt trace_rewrite_positive_lits then trace_msg ctxt msg else ();
fun trace_msg_rewrite_negative_lits ctxt msg = if Config.get ctxt trace_rewrite_negative_lits then trace_msg ctxt msg else ();
fun trace_msg_positive_simplify_reflect ctxt msg = if Config.get ctxt trace_positive_simplify_reflect then trace_msg ctxt msg else ();
fun trace_msg_negative_simplify_reflect ctxt msg = if Config.get ctxt trace_negative_simplify_reflect then trace_msg ctxt msg else ();
fun trace_msg_simp_outer_claus ctxt msg = if Config.get ctxt trace_simp_outer_claus then trace_msg ctxt msg else ();
fun trace_msg_simp_bool_rw ctxt msg = if Config.get ctxt trace_simp_bool_rw then trace_msg ctxt msg else ();
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
      ( "Not a valid jeha proof reconstruction mode: "
      ^ s
      ^ " (must be either of \"cheat\", \"argo\", \"metis\", \"blast\" or \"manual\")" )

val proof_reconstruction =
  Attrib.setup_config_string
    \<^binding>\<open>jeha_proof_reconstruction\<close>
    (K (string_of_proof_reconstruction_mode Manual))
(* val proof_reconstruction = Attrib.setup_config_bool \<^binding>\<open>jeha_proof_reconstruction\<close> (K true) *)

fun get_proof_reconstruction_mode ctxt = parse_proof_reconstruction_mode (Config.get ctxt proof_reconstruction)

(* FIXME: remove or better default *)
val max_number_of_steps = Attrib.setup_config_int \<^binding>\<open>jeha_max_number_of_steps\<close> (K 300)

(* NOTE: The rules aren't actually all turned off unless disable_all is set. *)
val disable_all = Attrib.setup_config_bool \<^binding>\<open>jeha_disable_all\<close> (K false)

val rule_default = false

(* inferences *)
val rule_sup = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_sup\<close> (K rule_default)
val rule_fluid_sup = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_fluid_sup\<close> (K rule_default)
val rule_e_res = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_e_res\<close> (K rule_default)
val rule_e_fact = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_e_fact\<close> (K rule_default)
val rule_arg_cong = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_arg_cong\<close> (K rule_default)
val rule_bool_hoist = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_bool_hoist\<close> (K rule_default)
val rule_false_elim = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_false_elim\<close> (K rule_default)
val rule_eq_hoist = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_eq_hoist\<close> (K rule_default)
val rule_neq_hoist = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_neq_hoist\<close> (K rule_default)
val rule_forall_hoist = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_forall_hoist\<close> (K rule_default)
val rule_exists_hoist = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_exists_hoist\<close> (K rule_default)
val rule_bool_rw = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_bool_rw\<close> (K rule_default)
val rule_forall_rw = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_forall_rw\<close> (K rule_default)
val rule_exists_rw = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_exists_rw\<close> (K rule_default)
val rule_fluid_bool_hoist = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_fluid_bool_hoist\<close> (K rule_default)
val rule_fluid_loob_ho = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_fluid_loob_hoist\<close> (K rule_default)
val rule_ext = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_ext\<close> (K rule_default)
val rule_neg_ext = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_neg_ext\<close> (K rule_default)
val rule_choice = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_choice\<close> (K rule_default)
(* simplifications *)
val rule_delete_duplicated_lits = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_delete_duplicated_lits\<close> (K rule_default)
val rule_delete_resolved_lits = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_delete_resolved_lits\<close> (K rule_default)
val rule_rewrite_positive_lits = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_rewrite_positive_lits\<close> (K rule_default)
val rule_rewrite_negative_lits = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_rewrite_negative_lits\<close> (K rule_default)
val rule_positive_simplify_reflect = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_positive_simplify_reflect\<close> (K rule_default)
val rule_negative_simplify_reflect = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_negative_simplify_reflect\<close> (K rule_default)
val rule_simp_outer_claus = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_simp_outer_claus\<close> (K rule_default)
val rule_simp_bool_rw = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_simp_bool_rw\<close> (K rule_default)
val rule_simp_false_elim = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_simp_false_elim\<close> (K rule_default)
val rule_syntactic_tautology_deletion1 = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_syntactic_tautology_deletion1\<close> (K rule_default)
val rule_syntactic_tautology_deletion2 = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_syntactic_tautology_deletion2\<close> (K rule_default)
val rule_clause_subsumption = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_clause_subsumption\<close> (K rule_default)
val rule_equality_subsumption = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_equality_subsumption\<close> (K rule_default)

val select_negativoid = Attrib.setup_config_bool \<^binding>\<open>jeha_select_negativoid\<close> (K true)
val select_flex_sided = Attrib.setup_config_bool \<^binding>\<open>jeha_select_flex_sided\<close> (K false)
val literal_selection_function = Attrib.setup_config_string \<^binding>\<open>jeha_literal_selection_function\<close> (K "select_first_neg_lit")

val unify_search_bound = Attrib.setup_config_int \<^binding>\<open>jeha_unify_search_bound\<close> (K 50)
val unify_timeout_ms = Attrib.setup_config_int \<^binding>\<open>jeha_unify_timeout_ms\<close> (K 10)
val supress_unify_trace = Attrib.setup_config_bool \<^binding>\<open>jeha_supress_unify_trace\<close> (K true)

val debug_check_clauses = Attrib.setup_config_bool \<^binding>\<open>jeha_debug_check_clauses\<close> (K false)

(** term parsing antiquotations **)

(* From the cookbook. Use

setup \<open> Jeha_Common.term_pat_setup \<close>

setup \<open> Jeha_Common.type_pat_setup \<close>

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

setup \<open> Jeha_Common.term_schem_setup \<close>

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

fun pretty_tyenv ctxt tyenv =
let
  fun get_typs (v, (s, T)) = (TVar (v, s), T)
  val print = apply2 (Syntax.pretty_typ ctxt)
in
  "tyenv:" ^ Pretty.string_of (pretty_helper (print o get_typs) tyenv)
end

fun pretty_tenv ctxt tenv =
let
  fun get_trms (v, (T, t)) = (Var (v, T), t)
  val print = apply2 (Syntax.pretty_term ctxt)
in
  "tenv:" ^ Pretty.string_of (pretty_helper (print o get_trms) tenv)
end;

(* from the cookbook
(* switch to unpretty printer *)
ML_system_pp (fn _ => fn _ => Pretty.to_polyml o Jeha_Common.raw_pp_typ);
ML_system_pp (fn _ => fn _ => Pretty.to_polyml o Jeha_Common.raw_pp_term);
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
            \<^assert> (String.isPrefix "jeha_trace_" name);
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
