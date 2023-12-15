signature JEHA_GEN_TERM =
sig
  type unif_state = (Proof.context * Type.tyenv * int)
  type 'a unif_gen = ('a, unif_state * SpecCheck_Random.rand) SpecCheck_Gen_Types.gen_state
  val term : typ list -> typ -> term unif_gen
  val fresh_tvar : typ unif_gen
end

structure Jeha_Gen_Term : JEHA_GEN_TERM =
struct

(* CONFIGURATION *)

(* probability of generating a schematic variable *)
val prob_of_var = 0.1
(* Precomputed, from the paper, presumably increasing the probability of
boltzmann_index leads to smaller terms. Weaker effect when increasing the
probability of boltzmann_lambda. *)
(* Scale precomputed values into interval determined by 1 - prob_of_var. *)
fun rescale r = (1.0 - prob_of_var) * r + prob_of_var
fun boltzmann_var r = r < prob_of_var
fun boltzmann_index r = r < rescale 0.35700035696434995;
fun boltzmann_lambda r = r < rescale 0.6 (* 0.6525813160382378 *);
(* The probability p of de Bruijn index 0, generally Bound j has the
probability (1-p)^j * p (geometric distribution) *)
fun boltzmann_leaf r = r < rescale 0.65 (* 0.7044190409261122 *);

(* PROPER *)

(* Adds unused additional state to a generator. Allows us to reuse existing
generators. *)
val lift_gen : ('a, 's) SpecCheck_Gen_Types.gen_state -> ('a, 'b * 's) SpecCheck_Gen_Types.gen_state =
  fn gen => (fn (b, s) => let val (a, s) = gen s in (a, (b, s)) end)

type unif_state = (Proof.context * Type.tyenv * int)

val add_unif : (typ * typ) -> unif_state -> unif_state =
  fn T_pair => fn (ctxt, typ_env, maxidx) =>
    let
      val (typ_env, maxidx) =
        Sign.typ_unify
          (Proof_Context.theory_of ctxt)
          T_pair
          (typ_env, maxidx)
    in
      (ctxt, typ_env, maxidx)
    end

(* Like gen but with unification state. *)
type 'a unif_gen = ('a, unif_state * SpecCheck_Random.rand) SpecCheck_Gen_Types.gen_state

val fresh_type_indexname : indexname unif_gen =
  fn ((ctxt, typ_env, maxidx), s) =>
    ((Name.aT, maxidx), ((ctxt, typ_env, maxidx + 1), s))

val defaultS : sort unif_gen = fn (s as ((ctxt, _, _), _)) =>
  (Sign.defaultS (Proof_Context.theory_of ctxt), s)

val fresh_tvar : typ unif_gen =
  SpecCheck_Gen_Term.tvar
    fresh_type_indexname
    defaultS

val fresh_var_indexname : indexname unif_gen =
  fn ((ctxt, typ_env, maxidx), s) =>
    (("x", maxidx), ((ctxt, typ_env, maxidx + 1), s))

(* Each term generator guarantees that it generates a term whose type unifies
with the type T in the type environment it returns (unless it fails). *)
fun term Ts T s =
  let
    val (r, s) = lift_gen (SpecCheck_Generator.range_real (0.0, 1.0)) s
  in
    if boltzmann_var r
      then var Ts T s
    else if boltzmann_index r
      then bound Ts T s
    else if boltzmann_lambda r
      then abs Ts T s
    else app Ts T s
  end

and var _ T s =
  let
    val (v, s) = fresh_var_indexname s
  in
    (Var (v, T), s)
  end

and bound [] _ _ = error "bound: not below lambda"
  | bound (bT::bound_Ts) T (unif_s, rng_s) =
      let val (r, rng_s) = SpecCheck_Random.real_unit rng_s in
        if boltzmann_index r
          then (Bound 0, (add_unif (bT, T) unif_s, rng_s))
          else
            SpecCheck_Generator.map
              (fn Bound i => Bound (i + 1))
              (bound bound_Ts T)
              (unif_s, rng_s)
      end

and abs Ts T s =
  let
    val (arg_T, s) = fresh_tvar s
    val (return_T, s) = fresh_tvar s
    val (unif_s, rng_s) = s
    val s = ()
    val unif_s = add_unif (arg_T --> return_T, T) unif_s
  in
    SpecCheck_Generator.map
      (fn t => Abs ("x" (* Name.uu_ *), arg_T, t))
      (term (arg_T :: Ts) return_T)
      (unif_s, rng_s)
  end

and app Ts T s =
  let
    val (arg_T, s) = fresh_tvar s
    val fun_T = arg_T --> T
  in
    SpecCheck_Generator.map
      op$
      (SpecCheck_Generator.zip (term Ts fun_T) (term Ts arg_T))
      s
  end

(* OLD *)

(* (rng state, env, maxidx) *)
type term_state = SpecCheck_Random.rand * Type.tyenv * int;

fun pick_index _ [] _ _ = error "pick_index: not below lambda"
  | pick_index (ctxt : Proof.context) (T::Ts) typ (s, env) =
  let
    val (r, s) = SpecCheck_Generator.range_real (0.0, 1.0) s
  in
    if boltzmann_leaf r
      then ((s, Sign.typ_unify (Proof_Context.theory_of ctxt) (T, typ) env), Bound 0)
      else
        let val (state, Bound i) = pick_index ctxt Ts typ (s, env) in
          (state, Bound (i+1))
        end
  end;

fun gen_fresh_tyvar ctxt maxidx =
  (maxidx + 1, TVar ((Name.aT, maxidx + 1), Sign.defaultS (Proof_Context.theory_of ctxt)));

fun ran_constant ctxt typ (s, (typ_env, maxidx)) =
  let
    fun upshift_TVar j (TVar ((name, i), T)) = TVar ((name, i + j), T)
      | upshift_TVar _ T = T
    fun map_const f (t as (Const _)) = f t
      | map_const _ t = t
    val freshen_type = map_const (map_types (map_atyps (upshift_TVar maxidx)))
    val constants =
      ctxt
      |> Proof_Context.theory_of
      |> Sign.consts_of
      |> Consts.dest
      |> #constants
      (* discard Pure... constants, length of 11 is a good cutoff that includes HOL.False *)
      |> filter (fn (name, _) => String.isPrefix "HOL" name andalso String.size name <= 11)
      (* |> filter (fn (name, _) => String.isPrefix "HOL.All" name orelse String.isPrefix "HOL.False" name) *)
      |> map (fn (name, (T, _)) => Const (name, T))
      (* |> curry (op @) [Free ("c", TVar (("'a", 0), [])), Free ("d", TVar (("'b", 0), []))] *)
    val (constant, s) = SpecCheck_Generator.elementsL constants s
    val constant = freshen_type constant
    val T = fastype_of constant
    val maxidx = Term.maxidx_typ T maxidx
    val (typ_env, maxidx) =
      Sign.typ_unify
        (Proof_Context.theory_of ctxt)
        (T, typ)
        (typ_env, maxidx)
  in
    ((s, (typ_env, maxidx)), constant)
  end

(* Generate a typable, closed random term. Rejection sampler with early abort
that fails via exceptions. *)
fun ran_typable
      (ctxt : Proof.context)
      (binder_types : typ list)
      (typ : typ)
      ((s, (typ_env, maxidx)) : SpecCheck_Random.rand * (Type.tyenv * int))
      : (SpecCheck_Random.rand * (Type.tyenv * int)) * term =
  let
    val (r, s) = SpecCheck_Generator.range_real (0.0, 1.0) s
  in
    if boltzmann_var r
      then ran_constant ctxt typ (s, (typ_env, maxidx))
    else if boltzmann_index r
      then pick_index ctxt binder_types typ (s, (typ_env, maxidx))
    else if boltzmann_lambda r
      then
        let
          val (maxidx, arg_T) = gen_fresh_tyvar ctxt maxidx
          val (maxidx, return_T) = gen_fresh_tyvar ctxt maxidx
          (* The type of the thing we're generating. *)
          val lambda_typ = arg_T --> return_T
          (* The `typ` we were asked to return must unify the type we're
          actually generating *)
          val (typ_env, maxidx) =
            Sign.typ_unify
              (Proof_Context.theory_of ctxt)
              (lambda_typ, typ)
              (typ_env, maxidx)
          val (state, body) =
            ran_typable
              ctxt
              (arg_T :: binder_types)
              return_T
              (s, (typ_env, maxidx))
        in
          (state, Abs (Name.uu_, arg_T, body))
        end
    else
      let
        val (maxidx, arg_T) = gen_fresh_tyvar ctxt maxidx
        val (state, function) =
          ran_typable ctxt binder_types (arg_T --> typ) (s, (typ_env, maxidx))
        val (state, arg) =
          ran_typable ctxt binder_types arg_T state
      in
        (state, function $ arg)
      end
  end

end;
