signature JLIT =
sig
  type T
  (* left or right side of an equational literal *)
  datatype lpos = Left | Right
  val is_positive : T -> bool
  val of_term : term -> T
  val lposs_of : T -> lpos list
  val map : (term -> term) -> T -> T
  val aconv : T * T -> bool
  val swap : T -> T
  val swap_lpos : lpos -> lpos
  (* make predicate literal, by equating the term to the boolean *)
  val mk_pred : term -> bool -> T
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

fun map f (s, t, b) = (f s, f t, b)

fun lposs_of _ = [Left, Right]

(* turn a boolean term into an equational literal *)
fun of_term t =
  let
    fun lit_of_aux b (Const (@{const_name HOL.eq}, _) $ s $ t) = (s, t, b)
      | lit_of_aux b (@{term Not} $ t) = lit_of_aux (not b) t
      (* FIXME: Should we prefer equation to disequations when injecting booleans? *)
      (* FIXME: us mk_pred_lit here? *)
      | lit_of_aux b t = (t, if b then @{term True} else @{term False}, true)
  in
    if not (fastype_of t = @{typ bool})
      then error "can only turn boolean terms into clauses"
      else lit_of_aux true t
  end

fun aconv ((s, t, b), (s', t', b')) =
  b = b' andalso
    (Term.aconv (s, s') andalso Term.aconv (t, t') orelse Term.aconv (s, t') andalso Term.aconv (t, s'))

fun swap (s, t, b) = (t, s, b)

fun swap_lpos Left = Right
  | swap_lpos Right = Left

(* Make equality between term and HOL Boolean, removing a prefix of negations from the term. *)
(* FIXME: is turning \<not>s \<approx> \<bottom> into s \<approx> \<top> okay? Should we use disequations instead of equations?
(see similar comment in dest_eq_bool_lit) *)
fun mk_pred (@{term Not} $ t) b = mk_pred t (not b)
  | mk_pred t b = (t, if b then @{term True} else @{term False}, true)

fun term_of (s, t, b) = (if b then I else HOLogic.mk_not) (HOLogic.mk_eq (s, t))

fun term_at_lpos (l, _, _) Left = l
  | term_at_lpos (_, r, _) Right = r

fun orient Left (l, r, b) = (l, r, b)
  | orient Right (l, r, b) = (r, l, b)

fun map_at_lpos Left f (l, r, b) = (f l, r, b)
  | map_at_lpos Right f (l, r, b) = (l, f r, b)

fun occurs_deeply_in x (l, r, _) = JTerm.occurs_deeply_in x l orelse JTerm.occurs_deeply_in x r

fun maxidx_of (s, t, _) = Int.max (apply2 maxidx_of_term (s, t))

(* see notes in info/master/kbo/build/main.pdf *)
fun kbo (st as (s, t, st_pos), uv as (u, v, uv_pos)) =
  if not st_pos andalso uv_pos
    (* compare negative to positive (note: never equal) *)
    then
      (* FIXME: merge the two traversals into one *)
      if [u, v] |> forall (fn n => [s, t] |> exists (fn m =>
          the_default false (Jeha_Common.map_some is_greater_equal (Jeha_Order.kbo (m, n)))))
        (* negative > positive iff. \<forall>\<dots>\<exists>\<dots> m \<ge> n *)
        then SOME GREATER
      else if [u, v] |> forall (fn n => [s, t] |> exists (fn m =>
                the_default false (Jeha_Common.map_some is_less (Jeha_Order.kbo (m, n)))))
        (* negative < positive iff. \<forall>\<dots>\<exists>\<dots> m > n *)
        then SOME LESS
      else NONE
  else if st_pos andalso not uv_pos
    (* compare positive to negative by swapping and reversing the result *)
    then Jeha_Common.map_some rev_order (kbo (uv, st))
  (* same signs *)
  else Jeha_Order.mk_multiset_order_of_strict Jeha_Order.kbo ([s, t], [u, v])

(* see notes in info/master/kbo/build/main.pdf *)
fun kbo_generic cmp (st as (s, t, st_pos), uv as (u, v, uv_pos)) =
  if not st_pos andalso uv_pos
    (* compare negative to positive (note: never equal) *)
    then
      (* FIXME: merge the two traversals into one *)
      if [u, v] |> forall (fn n => [s, t] |> exists (fn m =>
          the_default false (Jeha_Common.map_some is_greater_equal (cmp (m, n)))))
        (* negative > positive iff. \<forall>\<dots>\<exists>\<dots> m \<ge> n *)
        then SOME GREATER
      else if [u, v] |> forall (fn n => [s, t] |> exists (fn m =>
                the_default false (Jeha_Common.map_some is_less (cmp (m, n)))))
        (* negative < positive iff. \<forall>\<dots>\<exists>\<dots> m > n *)
        then SOME LESS
      else NONE
  else if st_pos andalso not uv_pos
    (* compare positive to negative by swapping and reversing the result *)
    then Jeha_Common.map_some rev_order (kbo_generic cmp (uv, st))
  (* same signs *)
  else Jeha_Order.mk_multiset_order_of_strict cmp ([s, t], [u, v])

fun pretty_lit' ctxt = Jeha_Common.pretty_term' ctxt o term_of

val pretty_lit = Pretty.string_of oo pretty_lit'

end;