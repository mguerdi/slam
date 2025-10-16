signature JLIT =
sig
  type T
  val mk : term * term * bool -> T 
  val dest : T -> term * term * bool
  val fold : (term -> 'a -> 'a) -> T -> 'a -> 'a
  val any_side : (term -> bool) -> T -> bool
  val both_sides : (term -> bool) -> T -> bool
  (* left or right side of an equational literal *)
  datatype lpos = Left | Right
  val is_positive : T -> bool
  val is_negative : T -> bool
  val is_negative_or_negativoid_cfg : Proof.context -> T -> bool
  val is_flex_sided : T -> bool
  val is_flex_flex : T -> bool
  val of_term_signed : bool -> term -> T
  val of_term : term -> T
  val lposs_of : T -> lpos list
  val map : (term -> term) -> T -> T
  val aconv : T * T -> bool
  val aconv_as : T * T -> lpos option
  val swap : T -> T
  val negate : T -> T
  val swap_lpos : lpos -> lpos
  (* make predicate literal, by equating the term to the boolean *)
  val mk_eq : term -> term -> T
  val mk_neq : term -> term -> T
  val mk_pred : term -> bool -> T
  val is_pred : T -> bool
  val dest_pred : T -> term * term
  val norm_negative_pred : T -> T
  val norm_beta_eta_qeta_env : Envir.env -> T -> T
  val term_of : T -> term
  val as_tpos : bool -> lpos -> JTerm.tpos
  val term_at_lpos : T -> lpos -> term
  val orient : lpos -> T -> T
  val map_at_lpos : lpos -> (term -> term) -> T -> T
  val occurs_deeply_in : term -> T -> bool
  val maxidx_of : T -> int
  val kbo : T * T -> Slam_Order.partial_order
  val kbo_generic :
    (('a * 'a) -> Slam_Order.partial_order) ->
    (('a * 'a * bool) * ('a * 'a * bool)) ->
    Slam_Order.partial_order
  val kbo_compare_left_to_right : T -> Slam_Order.partial_order
  val pretty_lit' : Proof.context -> T -> Pretty.T
  val pretty_lit : Proof.context -> T -> string
  val pretty_subterm' : Proof.context -> T -> lpos * JTerm.tpos -> Pretty.T
  val pretty_subterm : Proof.context -> T -> lpos * JTerm.tpos -> string
  val as_oriented_for_pretty : T -> lpos -> term
  val pretty_oriented' : Proof.context -> T -> lpos -> Pretty.T
  val pretty_oriented : Proof.context -> T -> lpos -> string
end;

structure JLit : JLIT =
struct

(* a known orientation *)
datatype orientation = LeftGreater | RightGreater | Equal

fun impl_swap_orientation LeftGreater = RightGreater
  | impl_swap_orientation RightGreater = LeftGreater
  | impl_swap_orientation Equal = Equal

val swap_orientation = Lazy.map (Option.map impl_swap_orientation)

datatype T =
  Lit of
    { lhs: term
    , rhs: term
    , pol: bool
    , orientation: orientation option Lazy.lazy
    , terms_normed: bool
    }

datatype lpos = Left | Right

fun compute_orientation_lazy lhs rhs = Lazy.lazy (fn () =>
  case Slam_KBO.ord (lhs, rhs) of
    SOME GREATER => SOME LeftGreater
  | SOME EQUAL => SOME Equal
  | SOME LESS => SOME RightGreater
  | NONE => NONE
)

fun mk (lhs, rhs, is_positive) =
  Lit { lhs = lhs, rhs = rhs, pol = is_positive, orientation = compute_orientation_lazy lhs rhs, terms_normed = false }

(* FIXME: deprecate? *)
fun dest (Lit { lhs, rhs, pol, ... }) = (lhs, rhs, pol)

fun fold f (Lit { lhs, rhs, ... }) = f lhs #> f rhs

fun any_side p (Lit { lhs, rhs, ... }) = p lhs orelse p rhs

fun both_sides p (Lit { lhs, rhs, ... }) = p lhs andalso p rhs

fun is_positive (Lit { pol, ... }) = pol

val is_negative = not o is_positive

fun is_negativoid (l as Lit { lhs, rhs, ... }) =
  is_negative l
    orelse JTerm.is_false lhs andalso not (JTerm.is_false rhs)
    orelse JTerm.is_false rhs andalso not (JTerm.is_false lhs)

fun is_negative_or_negativoid_cfg ctxt =
  if Config.get ctxt (Slam_Common.select_negativoid)
    then is_negativoid
    else is_negative

val is_flex_sided = any_side JTerm.is_variable_headed

val is_flex_flex = both_sides JTerm.is_variable_headed

(* forgets orientation *)
fun map f (Lit { lhs, rhs, pol, ... }) = mk (f lhs, f rhs, pol)

fun unsafe_map f (Lit { lhs, rhs, pol, orientation, terms_normed }) =
  Lit { lhs = f lhs, rhs = f rhs, pol = pol, orientation = orientation, terms_normed = terms_normed }

fun lposs_of _ = [Left, Right]

fun mk_eq lhs rhs = mk (lhs, rhs, true)

fun mk_neq lhs rhs = mk (lhs, rhs, false)

(* Make equality between term and HOL Boolean, removing a prefix of negations from the term. *)
(* FIXME: is turning \<not>s \<approx> \<bottom> into s \<approx> \<top> okay? Should we use disequations instead of equations?
(see similar comment in dest_pred) *)
fun mk_pred (@{term Not} $ t) b = mk_pred t (not b)
  | mk_pred t b = mk (t, if b then @{term True} else @{term False}, true)

fun of_term_signed b (Const (@{const_name HOL.eq}, _) $ lhs $ rhs) = mk (lhs, rhs, b)
  | of_term_signed b (Const (@{const_name HOL.Not}, _) $ t) = of_term_signed (not b) t
  (* FIXME: might need to revert this because mk_pred removes negations from t. *)
  | of_term_signed b t = mk_pred t b

(* turn a boolean term into an equational literal *)
fun of_term t =
  if not (fastype_of t = @{typ bool})
    then error "can only turn boolean terms into literals"
    else of_term_signed true t

fun aconv_as (Lit { lhs = s, rhs = t, pol = b, ... }, Lit { lhs = s', rhs = t', pol = b', ... }) =
  if b <> b' then NONE
  else if Term.aconv (s, s') andalso Term.aconv (t, t') then SOME Left
  else if Term.aconv (s, t') andalso Term.aconv (t, s') then SOME Right
  else NONE

val aconv = is_some o aconv_as

fun swap (Lit { lhs, rhs, pol, orientation, terms_normed }) =
  Lit { lhs = rhs, rhs = lhs, pol = pol, orientation = swap_orientation orientation, terms_normed = terms_normed }

fun negate (Lit { lhs, rhs, pol, orientation, terms_normed }) =
  (Lit { lhs = lhs, rhs = rhs, pol = not pol, orientation = orientation, terms_normed = terms_normed })

fun swap_lpos Left = Right
  | swap_lpos Right = Left

fun is_pred lit = is_positive lit andalso any_side JTerm.is_truth_value lit

fun dest_pred (Lit { lhs, rhs, pol = true, ... }) =
  (* FIXME: what about when both are truth values? do we prefer an orientation? *)
  if JTerm.is_truth_value rhs
    then (lhs, rhs)
  else if JTerm.is_truth_value lhs
    then (rhs, lhs)
  else error "neither is HOL.True or HOL.False"
  (* FIXME: allow disequations? (see similar comment above mk_pred) *)
  | dest_pred _ = error "disequation"

(* FIXME: If we used the correct literal order these two
\<top> \<noteq> \<top> \<mapsto> \<top> = \<bottom>
\<top> \<noteq> \<bottom> \<mapsto> \<top> = \<top>
would probably not be valid simplifications (the conclusion is not smaller than the premise). Thus
?x \<noteq> \<top> \<mapsto> x = \<bottom>
?x a b c \<noteq> \<top> \<mapsto> ...
aren't either.
The function below disallows the non-simplifications w.r.t. the current literal ordering (or at least
its implementaiton) 
*)
(* FIXME: maybe change our definition of "predicate literal" to include disequations and consolidate" *)
fun norm_negative_pred (l as Lit { pol = true, ... }) = l
  | norm_negative_pred (l as Lit { lhs = s, rhs = t, pol = false, ... }) =
      if JTerm.is_truth_value s andalso JTerm.ml_bool_of s andalso JTerm.is_variable_headed t
        then l
      else if JTerm.is_truth_value t andalso JTerm.ml_bool_of t andalso JTerm.is_variable_headed s
        then l
      else if JTerm.is_truth_value s andalso JTerm.is_truth_value t andalso JTerm.ml_bool_of s andalso JTerm.ml_bool_of t
        then l
      else if JTerm.is_truth_value s
        then mk (JTerm.negate_hol_bool s, t, true)
      else if JTerm.is_truth_value t
        then mk (s, JTerm.negate_hol_bool t, true)
      else l

(* FIXME: use unsafe_map if we have stability under substitutions *)
(* FIXME: if the substitution is empty (FIXME: watch out for maxidxforcer), or the terms are ground,
skip, and in particular preserve orientation! *)
fun norm_beta_eta_qeta_env env = map (JTerm.norm_beta_eta_qeta_env env)

fun term_of (Lit { lhs = s, rhs = t, pol = b, ... }) =
  (if b then I else HOLogic.mk_not) (HOLogic.mk_eq (s, t))

(* law: term_at_lpos lp (s, t, b) = JTerm.subterm_at (as_tpos b lp) (term_of (s, t, b)) *)
fun as_tpos true Left = [1]
  | as_tpos true Right = [2]
  | as_tpos false Left = [1, 1]
  | as_tpos false Right = [1, 2]

fun term_at_lpos (Lit { lhs, ... }) Left = lhs
  | term_at_lpos (Lit { rhs, ... }) Right = rhs

fun orient Left lit = lit
  | orient Right lit = swap lit

fun dest_orient Left (Lit { lhs, rhs, pol, ... }) = (lhs, rhs, pol)
  | dest_orient Right (Lit { lhs, rhs, pol, ... }) = (rhs, lhs, pol)

(* forgets orientation *)
fun map_at_lpos Left f (Lit { lhs, rhs, pol, ... }) = mk (f lhs, rhs, pol)
  | map_at_lpos Right f (Lit { lhs, rhs, pol, ... }) = mk (lhs, f rhs, pol)

fun occurs_deeply_in x = any_side (JTerm.occurs_deeply_in x)

fun maxidx_of (Lit { lhs, rhs, ... }) = Int.max (apply2 maxidx_of_term (lhs, rhs))

fun kbo_generic_different_signs_greater cmp ((s, t, st_pos), (u, v, uv_pos)) =
  (* different signs => never equal *)
  if not st_pos andalso uv_pos
    (* negative > positive iff. \<forall>\<dots>\<exists>\<dots> m \<ge> n *)
    then [u, v] |> forall (fn n => [s, t] |> exists (fn m =>
          the_default false (Slam_Common.map_some is_greater_equal (cmp (m, n)))))
  else if st_pos andalso not uv_pos
    (* positive > negative iff. \<forall>\<dots>\<exists>\<dots> m > n *)
    then [u, v] |> forall (fn n => [s, t] |> exists (fn m =>
          the_default false (Slam_Common.map_some is_greater (cmp (m, n)))))
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
  else Slam_Order.mk_multiset_order_of_strict cmp ([s, t], [u, v])

val kbo = kbo_generic Slam_KBO.ord o apply2 dest

fun kbo_compare_left_to_right (Lit { orientation, ... }) =
  case Lazy.force orientation of
    SOME LeftGreater => SOME GREATER
  | SOME RightGreater => SOME LESS
  | SOME Equal => SOME EQUAL
  | NONE => NONE

fun pretty_lit' ctxt = Slam_Common.pretty_term' ctxt o term_of

val pretty_lit = Pretty.string_of oo pretty_lit'

fun pretty_subterm' ctxt lit (lp, tp) =
  let
    val as_term = term_of lit
    val lp_as_tp = as_tpos (is_positive lit) lp @ tp
  in
    JTerm.pretty_subterm' ctxt as_term lp_as_tp
  end

val pretty_subterm = Pretty.string_of ooo pretty_subterm'

fun as_oriented_for_pretty lit lp =
  let
    val (s, t, b) = dest (orient lp lit)
    val a = fastype_of s
  in
    \<^instantiate>\<open>'a=a and s and t in term \<open><s \<approx>> t>\<close>\<close>
  end

(* lp points to the lhs of the rewrite rule *)
fun pretty_oriented' ctxt lit lp = Slam_Common.pretty_term' ctxt (as_oriented_for_pretty lit lp)

val pretty_oriented = Pretty.string_of ooo pretty_oriented'

end;
