
signature JEHA_COMMON =
sig
  val trace : bool Config.T
  val trace_msg : Proof.context -> (unit -> string) -> unit
  val verbose_of : Proof.context -> Proof.context
  val pretty_term : Proof.context -> term -> string
  val pretty_typ : Proof.context -> typ -> string
  val pretty_terms : Proof.context -> term list -> string
  val pretty_tyenv : Proof.context -> Type.tyenv -> string
  val pretty_tenv : Proof.context -> Envir.tenv -> string
  val I : 'a -> 'a
  val map_some : ('a -> 'b) -> 'a option -> 'b option
  val seq_cartesian_product : 'a Seq.seq -> 'b Seq.seq -> ('a * 'b) Seq.seq
  val cartesian_product : 'a list -> 'b list -> ('a * 'b) list
  (* Config options to turn rules on and off. *)
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
  val rule_choice : bool Config.T
  val rule_delete_duplicated_lits : bool Config.T
  val rule_delete_resolved_lits : bool Config.T
  val rule_rewrite_positive_lits : bool Config.T
  val rule_rewrite_negative_lits : bool Config.T
  val rule_positive_simplify_reflect : bool Config.T
  val rule_negative_simplify_reflect : bool Config.T
  val rule_pos_outer_claus : bool Config.T
  val rule_neg_outer_claus : bool Config.T
  val rule_syntactic_tautology_deletion1 : bool Config.T
  val rule_syntactic_tautology_deletion2 : bool Config.T
  val rule_clause_subsumption : bool Config.T
  val rule_equality_subsumption : bool Config.T
  val disable_all : bool Config.T
end

structure Jeha_Common : JEHA_COMMON =
struct

(* for tracing *)
fun I x = x

(* from metis_generate.ML *)
val trace = Attrib.setup_config_bool \<^binding>\<open>jeha_trace\<close> (K false)
val verbose = Attrib.setup_config_bool \<^binding>\<open>jeha_verbose\<close> (K true)
fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ();

(* NOTE: The rules aren't actually all turned off unless disable_all is set. *)
val rule_default = false

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
val rule_choice = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_choice\<close> (K rule_default)
val rule_delete_duplicated_lits = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_delete_duplicated_lits\<close> (K rule_default)
val rule_delete_resolved_lits = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_delete_resolved_lits\<close> (K rule_default)
val rule_rewrite_positive_lits = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_rewrite_positive_lits\<close> (K rule_default)
val rule_rewrite_negative_lits = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_rewrite_negative_lits\<close> (K rule_default)
val rule_positive_simplify_reflect = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_positive_simplify_reflect\<close> (K rule_default)
val rule_negative_simplify_reflect = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_negative_simplify_reflect\<close> (K rule_default)
val rule_pos_outer_claus = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_pos_outer_claus\<close> (K rule_default)
val rule_neg_outer_claus = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_neg_outer_claus\<close> (K rule_default)
val rule_syntactic_tautology_deletion1 = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_syntactic_tautology_deletion1\<close> (K rule_default)
val rule_syntactic_tautology_deletion2 = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_syntactic_tautology_deletion2\<close> (K rule_default)
val rule_clause_subsumption = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_clause_subsumption\<close> (K rule_default)
val rule_equality_subsumption = Attrib.setup_config_bool \<^binding>\<open>jeha_rule_equality_subsumption\<close> (K rule_default)

val disable_all = Attrib.setup_config_bool \<^binding>\<open>jeha_disable_all\<close> (K false)

(* much from cookboock *)
fun verbose_of ctxt = config_put_many_bool ctxt
  [show_types, show_brackets, show_markup, show_sorts, show_structs]
and config_put_many_bool ctxt options =
  List.foldr (fn (option, ctxt) => Config.put option true ctxt) ctxt options

fun pretty_term ctxt t = Syntax.pretty_term ctxt t |> Pretty.string_of

fun pretty_typ ctxt T = Syntax.pretty_typ ctxt T |> Pretty.string_of

fun pretty_terms ctxt terms =
  terms
  |> map (Syntax.pretty_term ctxt)
  |> Pretty.commas |> Pretty.block |> Pretty.string_of

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

fun map_some _ NONE = NONE
  | map_some f (SOME x) = SOME (f x)

fun seq_cartesian_product xs ys =
  case Seq.pull xs of
    SOME (x, xs) => Seq.append (Seq.map (pair x) ys) (seq_cartesian_product xs ys)
  | NONE => Seq.empty

fun cartesian_product [] _ = []
  | cartesian_product (x :: xs) ys = map (pair x) ys @ cartesian_product xs ys

end