(* Wrappers around Isabelles unfication functions. *)
signature SLAM_UNIFY =
sig
  (* from unify.ML *)
  val smash_unifiers: Context.generic -> (term * term) list -> Envir.env -> Envir.env Seq.seq
  (* list of flex-flex pairs to which the substitution has been applied *)
  type preunifier = Envir.env * (term * term) list
  val preunifiers : Context.generic -> (term * term) list -> Envir.env -> preunifier Seq.seq
  val shallow_first_smash_unifiers : Context.generic -> (term * term) list -> Envir.env -> Envir.env Seq.seq
  (* from more_unify.ML *)
  val matchers: Context.generic -> int -> (term * term) list -> Envir.env Seq.seq
  val shallow_first_matchers: Context.generic -> int -> (term * term) list -> Envir.env Seq.seq
  (* unification and matching of (symmetric!) equality literals *)
  val literal_smash_unifiers : Context.generic -> (JLit.T * JLit.T) -> Envir.env -> Envir.env Seq.seq
  val literal_shallow_first_smash_unifiers :
    Context.generic -> (JLit.T * JLit.T) -> Envir.env -> Envir.env Seq.seq
  val literal_matchers :
    Context.generic -> int -> (JLit.T * JLit.T) -> (JLit.lpos * Envir.env) Seq.seq
  val literal_shallow_first_matchers :
    Context.generic -> int -> (JLit.T * JLit.T) -> (JLit.lpos * Envir.env) Seq.seq
end

structure Slam_Unify : SLAM_UNIFY =
struct

fun with_timeout ctxt (xq : 'a Seq.seq) : 'a Seq.seq =
  let
    val timeout = Time.fromMilliseconds (Config.get_generic ctxt Slam_Common.unify_timeout_ms)
  in
    if timeout = Time.zeroTime
      then xq
      else
        Seq.make (fn () =>
          (case (Timeout.apply timeout Seq.pull) xq of
            NONE => NONE
          | SOME (x, xq') => SOME (x, with_timeout ctxt xq'))
          handle Timeout.TIMEOUT _ => NONE
        )
  end

(* Needed because of the following remark in unify.ML:
"The outermost functions assume the terms to be unified already have the same type." *)
fun give_to_undefined t =
  let
    val T = fastype_of t handle TERM e => (writeln ("BIG ERROR (TERM)" ^ @{make_string} t); raise TERM e)
  in
    (* FIXME: there might be a better approach *)
    (* use dummyT instead of unit to depend on less of HOL *)
    Const (@{const_name undefined}, T --> dummyT) $ t
  end

fun silence_context ctxt =
    if not (Config.get_generic ctxt Slam_Common.supress_unify_trace) then ctxt else
    (* disable very long Enter MATCH tracing messages when unification bound is exceeded *)
    (* based on slience_methods from try0.ML *)
    ctxt
    |> Context.the_proof
    |> Context_Position.set_visible false
    |> (fn ctxt => Config.put Slam_Isabelle_Unify.unify_trace_bound (Config.get ctxt Slam_Isabelle_Unify.search_bound) ctxt)
    |> Proof_Context.background_theory
        (fn thy => thy
          |> Context_Position.set_visible_global false
          |> Config.put_global Slam_Isabelle_Unify.unify_trace_bound (Config.get_global thy Slam_Isabelle_Unify.search_bound))
    |> Context.Proof

fun impl_smash_unifiers ctxt tus env =
  let
    (* val _ = Slam_Common.trace_msg (Context.the_proof ctxt) (fn () => "unifying: " ^ fold (curry (op ^)) (map ((fn (l, r) => l ^ " = " ^ r ^ ", ") o apply2 (Slam_Common.pretty_term (Context.the_proof ctxt))) tus) "") *)
    (* disable very long Enter MATCH tracing messages when unification bound is exceeded *)
    (* based on slience_methods from try0.ML *)
    val ctxt = silence_context ctxt
    val maxidx =
      fold
        (fn tu => fn maxidx => Int.max (maxidx, Int.max (apply2 maxidx_of_term tu)))
        tus
        ~1
    val env = Envir.merge (Envir.empty maxidx, env)
    val tus = map (apply2 give_to_undefined) tus
  in
    Slam_Isabelle_Unify.smash_unifiers ctxt tus env
  end

fun smash_unifiers ctxt = with_timeout ctxt oo impl_smash_unifiers ctxt

type preunifier = Envir.env * (term * term) list

(* Apply substitution to the flex-flex pairs, ensure that they are still flex-flex after. *)
fun to_preunifier ctxt (substitution, flex_flex_pairs) =
  let
    val normed_flex_flex_pairs = map (apply2 (Envir.norm_term substitution)) flex_flex_pairs
    fun is_variable_headed_application t =
      case t of (_ $ _) => JTerm.is_variable_headed t | _ => false
    fun is_flex_flex (Abs (_, _, s), Abs (_, _, t)) = is_flex_flex (s, t)
      | is_flex_flex (s, t) =
          is_variable_headed_application s andalso is_variable_headed_application t
    fun check_pair (i, (s, t)) =
      if is_flex_flex (s, t)
        then ()
        else warning (
          "to_preunifier: not a flex-flex pair: "
          ^ Slam_Common.pretty_term ctxt s ^ " =\<^sup>? " ^ Slam_Common.pretty_term ctxt t
          ^ " (previously " ^ let val (s', t') = nth flex_flex_pairs i in
            Slam_Common.pretty_term ctxt s' ^ " =\<^sup>? " ^ Slam_Common.pretty_term ctxt t'
          end ^ ")"
        )
    val () = List.app check_pair (map_index I normed_flex_flex_pairs)
  in
    (substitution, normed_flex_flex_pairs)
  end

fun impl_preunifiers ctxt tus env =
  let
    (* val _ = Slam_Common.trace_msg (Context.the_proof ctxt) (fn () => "unifying: " ^ fold (curry (op ^)) (map ((fn (l, r) => l ^ " = " ^ r ^ ", ") o apply2 (Slam_Common.pretty_term (Context.the_proof ctxt))) tus) "") *)
    (* disable very long Enter MATCH tracing messages when unification bound is exceeded *)
    (* based on slience_methods from try0.ML *)
    val ctxt = silence_context ctxt
    val maxidx =
      fold
        (fn tu => fn maxidx => Int.max (maxidx, Int.max (apply2 maxidx_of_term tu)))
        tus
        ~1
    val env = Envir.merge (Envir.empty maxidx, env)
    val tus = map (apply2 give_to_undefined) tus
  in
    Slam_Isabelle_Unify.unifiers (ctxt, env, tus)
    |> Seq.map (to_preunifier (Context.the_proof ctxt))
  end

fun preunifiers ctxt = with_timeout ctxt oo impl_preunifiers ctxt

fun upto_exp first last =
  if first < 0 orelse last < first then error ("first (" ^ @{make_string} first ^ ") or last (" ^ @{make_string} last ^ ") too small") else
  let
    val log_first = if first = 0 then ~1 (* e^-1 rounds to 0 *) else Real.round (Math.ln (Real.fromInt first))
    val log_last = Real.round (Math.ln (Real.fromInt last))
    val log_range = log_first upto log_last
    val range = map (Real.round o Math.exp o Real.fromInt) log_range
  in
    range
  end

(* Repeatedly calls the argument unif with increasing depths. Tests max depth first to quickly
identify if the problem is unifiable at all (within the maximal depth limit). *)
fun mk_impl_shallow_first ctxt (unif: int -> 'a Seq.seq) : 'a Seq.seq =
  let
    val max_depth :: rev_depths =
      rev (upto_exp 0 (Config.get_generic ctxt Slam_Common.unify_search_bound))
    val depths = Seq.of_list (rev rev_depths)
  in
    Seq.make (fn () =>
      (* FIXME: We need to make sure that the computation of this large-depth unifier can trigger the timeout! *)
      case Seq.pull (unif max_depth) of
        NONE => NONE
      | SOME (unifier, rest) =>
          Seq.append
            (Seq.maps unif depths)
            (Seq.append (Seq.single unifier) rest)
          |> Seq.pull
    )
  end

(* Repeatedly call unification algorithm with increasing unification search bounds. *)
fun impl_shallow_first_smash_unifiers ctxt tus env =
  mk_impl_shallow_first
    ctxt
    (fn search_bound =>
      impl_smash_unifiers (Config.put_generic Slam_Isabelle_Unify.search_bound search_bound ctxt) tus env)

fun shallow_first_smash_unifiers ctxt = with_timeout ctxt oo impl_shallow_first_smash_unifiers ctxt

fun impl_matchers ctxt maxidx pairs =
  let
    val maxidx = Int.max (maxidx, 0)
    val ctxt = silence_context ctxt
    (* ensures that fresh variables generated by Unify.smash_unifiers (called by
    Unify.matchers below) are greater than maxidx *)
    val v_pattern_indexname = ("maxidxforcer_pattern", maxidx)
    val v_pattern = Var (v_pattern_indexname, dummyT)
    val v_term = Var (("maxidxforcer_term", maxidx), dummyT)
    val pairs = map (apply2 give_to_undefined) ((v_pattern, v_term) :: pairs)
    fun remove_maxidxforcers (Envir.Envir { maxidx, tenv, tyenv }) =
      Envir.Envir { maxidx = maxidx, tenv = Vartab.delete v_pattern_indexname tenv, tyenv = tyenv }
  in
    Slam_Isabelle_Unify.matchers ctxt pairs
    |> Seq.map remove_maxidxforcers
  end

fun matchers ctxt = with_timeout ctxt oo impl_matchers ctxt

(* Repeatedly call matching algorithm with increasing unification search bounds. *)
fun impl_shallow_first_matchers ctxt maxidx pairs =
  mk_impl_shallow_first
    ctxt
    (fn search_bound =>
      impl_matchers (Config.put_generic Slam_Isabelle_Unify.search_bound search_bound ctxt) maxidx pairs)

fun shallow_first_matchers ctxt = with_timeout ctxt oo impl_shallow_first_matchers ctxt

fun mk_impl_literal_unifiers term_unifiers ctxt lit_pair env =
  let
    val ((s, t, b), (s', t', b')) = apply2 JLit.dest lit_pair
  in
    if not (b = b') then Seq.empty else
    Seq.interleave
      ( term_unifiers ctxt [(s, s'), (t, t')] env
      , term_unifiers ctxt [(s, t'), (t, s')] env )
  end

val impl_literal_smash_unifiers = mk_impl_literal_unifiers impl_smash_unifiers

fun literal_smash_unifiers ctxt = with_timeout ctxt oo impl_literal_smash_unifiers ctxt

val impl_literal_shallow_first_smash_unifiers =
  mk_impl_literal_unifiers impl_shallow_first_smash_unifiers

fun literal_shallow_first_smash_unifiers ctxt =
  with_timeout ctxt oo impl_literal_shallow_first_smash_unifiers ctxt

fun mk_impl_literal_matchers term_matchers ctxt maxidx lit_pair =
  let
    val ((s, t, b), (s', t', b')) = apply2 JLit.dest lit_pair
  in
    if not (b = b') then Seq.empty else
      ( [(s, s'), (t, t')]
      , [(s, t'), (t, s')] )
      |> apply2 (term_matchers ctxt maxidx)
      |> (fn (left_matchers, right_matchers) =>
        (Seq.map (pair JLit.Left) left_matchers, Seq.map (pair JLit.Right) right_matchers))
      |> Seq.interleave
  end

val impl_literal_matchers = mk_impl_literal_matchers impl_matchers

fun literal_matchers ctxt = with_timeout ctxt oo impl_literal_matchers ctxt

val impl_literal_shallow_first_matchers = mk_impl_literal_matchers impl_shallow_first_matchers

fun literal_shallow_first_matchers ctxt =
  with_timeout ctxt oo impl_literal_shallow_first_matchers ctxt

end
