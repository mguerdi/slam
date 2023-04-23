
signature JEHA_COMMON =
sig
  val trace : bool Config.T
  val trace_msg : Proof.context -> (unit -> string) -> unit
  val verbose_of : Proof.context -> Proof.context
  val pretty_term : Proof.context -> term -> string
  val pretty_terms : Proof.context -> term list -> string
  val pretty_tyenv : Proof.context -> Type.tyenv -> string
  val pretty_tenv : Proof.context -> Envir.tenv -> string
  val I : 'a -> 'a
end

structure Jeha_Common : JEHA_COMMON =
struct

(* for tracing *)
fun I x = x

(* from metis_generate.ML *)
val trace = Attrib.setup_config_bool \<^binding>\<open>jeha_trace\<close> (K false)
val verbose = Attrib.setup_config_bool \<^binding>\<open>jeha_verbose\<close> (K true)
fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ();

(* much from cookboock *)
fun verbose_of ctxt = config_put_many_bool ctxt
  [show_types, show_brackets, show_markup, show_sorts, show_structs]
and config_put_many_bool ctxt options =
  List.foldr (fn (option, ctxt) => Config.put option true ctxt) ctxt options

fun pretty_term ctxt t = Syntax.pretty_term ctxt t |> Pretty.string_of

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

end