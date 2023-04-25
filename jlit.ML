signature JLIT =
sig
  type T
  (* left or right side of an equational literal *)
  datatype lpos = Left | Right
  val of_term : term -> T
  val lposs_of : T -> lpos list
  val map_lit : (term -> term) -> T -> T
  val aconv_lit : T * T -> bool
  val swap_lit : T -> T
  val swap_lpos : lpos -> lpos
  val mk_lit_eq_bool : term -> bool -> T
  val term_of_lit : T -> term
  val term_at_lpos : T -> lpos -> term
  val map_at_lpos : lpos -> (term -> term) -> T -> T
  val occurs_deeply_in_lit : term -> T -> bool
end;

structure JLit : JLIT =
struct

type T = term * term * bool
datatype lpos = Left | Right

fun map_lit f (s, t, b) = (f s, f t, b)

fun lposs_of _ = [Left, Right]

(* turn a boolean term into an equational literal *)
fun of_term t =
  let
    fun lit_of_aux b (Const (@{const_name HOL.eq}, _) $ s $ t) = (s, t, b)
      | lit_of_aux b (@{term Not} $ t) = lit_of_aux (not b) t
      (* FIXME: Should we prefer equation to disequations when injecting booleans? *)
      | lit_of_aux b t = (t, if b then @{term True} else @{term False}, true)
  in
    if not (fastype_of t = @{typ bool})
      then error "can only turn boolean terms into clauses"
      else lit_of_aux true t
  end

fun aconv_lit ((s, t, b), (s', t', b')) =
  b = b' andalso
    (s aconv s' andalso t aconv t' orelse s aconv t' andalso t aconv t')

fun swap_lit (s, t, b) = (t, s, b)

fun swap_lpos Left = Right
  | swap_lpos Right = Left

(* Make equality between term and HOL Boolean, removing a prefix of negations from the term. *)
(* FIXME: is turning \<not>s \<approx> \<bottom> into s \<approx> \<top> okay? Should we use disequations instead of equations?
(see similar comment in dest_eq_bool_lit) *)
fun mk_lit_eq_bool (@{term Not} $ t) b = mk_lit_eq_bool t (not b)
  | mk_lit_eq_bool t b = (t, if b then @{term True} else @{term False}, true)

fun term_of_lit (s, t, b) = (if b then I else HOLogic.mk_not) (HOLogic.mk_eq (s, t))

fun term_at_lpos (l, _, _) Left = l
  | term_at_lpos (_, r, _) Right = r

fun map_at_lpos Left f (l, r, b) = (f l, r, b)
  | map_at_lpos Right f (l, r, b) = (l, f r, b)

fun occurs_deeply_in_lit x (l, r, _) = JTerm.occurs_deeply_in_term x l orelse JTerm.occurs_deeply_in_term x r

end;