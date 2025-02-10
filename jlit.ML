signature JLIT =
sig
  type T
  (* left or right side of an equational literal *)
  datatype lpos = Left | Right
  val is_positive : T -> bool
  val is_negative : T -> bool
  val of_term_signed : bool -> term -> T
  val of_term : term -> T
  val lposs_of : T -> lpos list
  val map : (term -> term) -> T -> T
  val aconv : T * T -> bool
  val aconv_as : T * T -> lpos option
  val swap : T -> T
  val swap_lpos : lpos -> lpos
  (* make predicate literal, by equating the term to the boolean *)
  val mk_pred : term -> bool -> T
  val is_pred : T -> bool
  val dest_pred : T -> term * term
  val norm_negative_pred : Proof.context -> T -> T
  val norm_beta_eta_qeta_env : Envir.env -> T -> T
  val term_of : T -> term
  val term_at_lpos : T -> lpos -> term
  val orient : lpos -> T -> term * term * bool
  val map_at_lpos : lpos -> (term -> term) -> T -> T
  val occurs_deeply_in : term -> T -> bool
  val maxidx_of : T -> int
  val kbo : T * T -> Jeha_Order.partial_order
  val kbo_generic :
    (('a * 'a) -> Jeha_Order.partial_order) ->
    (('a * 'a * bool) * ('a * 'a * bool)) ->
    Jeha_Order.partial_order
  val pretty_lit' : Proof.context -> T -> Pretty.T
  val pretty_lit : Proof.context -> T -> string
end;

structure JLit : JLIT =
struct

type T = term * term * bool
datatype lpos = Left | Right

fun is_positive (_, _, b) = b

val is_negative = not o is_positive

fun map f (s, t, b) = (f s, f t, b)

fun lposs_of _ = [Left, Right]

(* Make equality between term and HOL Boolean, removing a prefix of negations from the term. *)
(* FIXME: is turning \<not>s \<approx> \<bottom> into s \<approx> \<top> okay? Should we use disequations instead of equations?
(see similar comment in dest_pred) *)
fun mk_pred (@{term Not} $ t) b = mk_pred t (not b)
  | mk_pred t b = (t, if b then @{term True} else @{term False}, true)

fun of_term_signed b (Const (@{const_name HOL.eq}, _) $ s $ t) = (s, t, b)
  | of_term_signed b (Const (@{const_name HOL.Not}, _) $ t) = of_term_signed (not b) t
  (* FIXME: might need to revert this because mk_pred removes negations from t. *)
  | of_term_signed b t = mk_pred t b

(* turn a boolean term into an equational literal *)
fun of_term t =
  if not (fastype_of t = @{typ bool})
    then error "can only turn boolean terms into clauses"
    else of_term_signed true t

fun aconv_as ((s, t, b), (s', t', b')) =
  if b <> b' then NONE
  else if Term.aconv (s, s') andalso Term.aconv (t, t') then SOME Left
  else if Term.aconv (s, t') andalso Term.aconv (t, s') then SOME Right
  else NONE

val aconv = is_some o aconv_as

fun swap (s, t, b) = (t, s, b)

fun swap_lpos Left = Right
  | swap_lpos Right = Left

fun is_truth_value t = t = @{term True} orelse t = @{term False}

fun is_pred (s, t, true) = exists is_truth_value [s, t]
  | is_pred _ = false

fun dest_pred (s, t, true) =
  (* FIXME: what about when both are truth values? do we prefer an orientation? *)
  if is_truth_value t
    then (s, t)
  else if is_truth_value s
    then (t, s)
  else error "neither is HOL.True or HOL.False"
  (* FIXME: allow disequations? (see similar comment above mk_pred) *)
  | dest_pred _ = error "disequation"

(* FIXME: maybe change our definition of "predicate literal" to include disequations and consolidate" *)
fun norm_negative_pred ctxt (l as (_, _, true)) = l
  | norm_negative_pred ctxt (l as (s, t, false)) =
      if (Config.get ctxt Jeha_Common.no_norm_neg_pred_if_both_truth_values
          andalso is_truth_value s andalso is_truth_value t)
        then l
      else if is_truth_value s
        then (JTerm.negate_hol_bool s, t, true)
      else if is_truth_value t
        then (s, JTerm.negate_hol_bool t, true)
      else l 

fun norm_beta_eta_qeta_env env = map (JTerm.norm_beta_eta_qeta_env env)

fun term_of (s, t, b) = (if b then I else HOLogic.mk_not) (HOLogic.mk_eq (s, t))

fun term_at_lpos (l, _, _) Left = l
  | term_at_lpos (_, r, _) Right = r

fun orient Left (l, r, b) = (l, r, b)
  | orient Right (l, r, b) = (r, l, b)

fun map_at_lpos Left f (l, r, b) = (f l, r, b)
  | map_at_lpos Right f (l, r, b) = (l, f r, b)

fun occurs_deeply_in x (l, r, _) = JTerm.occurs_deeply_in x l orelse JTerm.occurs_deeply_in x r

fun maxidx_of (s, t, _) = Int.max (apply2 maxidx_of_term (s, t))

fun kbo_generic_different_signs_greater cmp ((s, t, st_pos), (u, v, uv_pos)) =
  (* different signs => never equal *)
  if not st_pos andalso uv_pos
    (* negative > positive iff. \<forall>\<dots>\<exists>\<dots> m \<ge> n *)
    then [u, v] |> forall (fn n => [s, t] |> exists (fn m =>
          the_default false (Jeha_Common.map_some is_greater_equal (cmp (m, n)))))
  else if st_pos andalso not uv_pos
    (* positive > negative iff. \<forall>\<dots>\<exists>\<dots> m > n *)
    then [u, v] |> forall (fn n => [s, t] |> exists (fn m =>
          the_default false (Jeha_Common.map_some is_greater (cmp (m, n)))))
  else error "kbo_generic_different_signs_greater: same signs"

(* see notes in info/master/kbo/build/main.pdf *)
fun kbo_generic cmp (st as (s, t, st_pos), uv as (u, v, uv_pos)) =
  if st_pos = not uv_pos
    then
      if kbo_generic_different_signs_greater cmp (st, uv)
        then SOME GREATER
      else if kbo_generic_different_signs_greater cmp (uv, st)
        then SOME LESS
      else NONE
  (* fall back to multiset comparison *)
  else Jeha_Order.mk_multiset_order_of_strict cmp ([s, t], [u, v])

val kbo = kbo_generic Jeha_Order.kbo

fun pretty_lit' ctxt = Jeha_Common.pretty_term' ctxt o term_of

val pretty_lit = Pretty.string_of oo pretty_lit'

end;
