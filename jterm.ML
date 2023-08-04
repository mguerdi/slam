signature JTERM =
sig
  (* type T = term *)
  type tpos = int list (* position of a subterm *)
  val is_quantifier : term -> bool
  val quantified_typ : term -> typ
  val strip_comb_fun_types_args : term -> term * typ list * term list
  val strip_comb_fun_types_args1 : typ list * term -> term * typ list * term list
  val is_variable_headed : term -> bool
  val is_position_of_fully_applied_logical_symbol : tpos -> term -> bool
  val tposs_of : term -> tpos list
  val disagreement_tpos_of2 : term * term -> tpos option
  val green_tposs_of : term -> tpos list
  val is_green_tpos : tpos -> term -> bool
  val subterm_at : term -> tpos -> term
  val map_at : tpos -> (term -> term) -> term -> term
  (* preprocessing *)
  val fold_non_greens_lvl : (int -> term -> 'a -> 'a) -> int -> term -> 'a -> 'a
  val fold_non_greens : (term -> 'a -> 'a) -> term -> 'a -> 'a
  val might_be_fluid : term -> bool
  val occurs_deeply_in : term -> term -> bool
  val norm_quantifier_poly_eq : term -> term
  (* normalization *)
  val norm_beta_eta_qeta_env : Envir.env -> term -> term
  val norm_beta_eta_qeta : term -> term
  val ensure_lambda_under_q : term -> term
end;

structure JTerm : JTERM =
struct

(* type T = term *)

fun is_quantifier (Const (@{const_name HOL.All}, _)) = true
  | is_quantifier (Const (@{const_name HOL.Ex}, _)) = true
  | is_quantifier _ = false

fun is_Abs (Abs _) = true
  | is_Abs _ = false

(* the type of the variable bound by the quantifier *)
fun quantified_typ (t as Const (_, T_to_bool_to_bool)) =
  if is_quantifier t
    then domain_type (domain_type (T_to_bool_to_bool))
    else error "not a quantifier"
  | quantified_typ _ = error ""

fun strip_comb_fun_types_args1 (boundTs, t) =
  let
    val (f, ts) = strip_comb t
    val types = fastype_of1 (boundTs, f) |> binder_types |> take (length ts)
  in
    (f, types, ts)
  end

(* Translates Isabelle/HOL application (f $ u\<^sub>1) $ u\<^sub>2) \<dots> to o\<lambda>Sup application f \<open>\<tau>\<^sub>1, \<tau>\<^sub>2\<close> u\<^sub>1 u\<^sub>2 \<dots> with
explicit type args. *)
fun strip_comb_fun_types_args t = strip_comb_fun_types_args1 ([], t)

(* Term position, mostly for documentation / testing purposes. See long comment at bottom. *)
type tpos = int list;

(* t|\<^sub>p *)
fun subterm_at t [] = t
  | subterm_at (Abs(_,_,u)) (0 :: p) = subterm_at u p
  (* FIXME: when you forget to bind the t (via as) there is no warning and when
  you call the function from somewhere else, where a t has been declared it uses
  that. Scoping broken?? *)
  | subterm_at (t as (_$_)) (i :: p) = subterm_at (nth (uncurry cons (strip_comb t)) i) p
  | subterm_at _ _ = error ""

fun tposs_of (Abs(_,_,u)) = [] :: map (cons 0) (tposs_of u)
  | tposs_of (t as (_$_)) =
    let
      val tposs_of_head_and_args : tpos list list = map tposs_of (uncurry cons (strip_comb t))
      val tposs_of_comb =
        (* prepend term position in the combination *)
        map_index (fn (idx, tposs_of_subterm) => map (cons idx) tposs_of_subterm)
          tposs_of_head_and_args
    in
      [] :: flat tposs_of_comb
    end
  | tposs_of _ = [[]]

(* NONE means no disagreement, the terms are the same *)
fun disagreement_tpos_of2 (Abs(_,_,t), Abs(_,_,u)) = Jeha_Common.map_some (cons 0) (disagreement_tpos_of2 (t, u))
  | disagreement_tpos_of2 (t as (_$_), u as (_$_)) =
    let
      val (head_args_t, head_args_u) = (apply2 (uncurry cons o strip_comb)) (t, u)
    in
      if length head_args_t <> length head_args_u then SOME [] else
      let
        val disagreement_tpos_of2_head_and_args : tpos option list =
          map disagreement_tpos_of2 (head_args_t ~~ head_args_u)
        val disagreement_tpos_of2_comb =
          (* prepend term position in the combination FIXME: just map_index pair and prepend in the case ... [()]*)
          map_index
            (fn (idx, disagreement_tpos_of2_subterm) =>
              Jeha_Common.map_some (cons idx) disagreement_tpos_of2_subterm)
            disagreement_tpos_of2_head_and_args
      in
        case (map_filter I disagreement_tpos_of2_comb) of
          (* no disagreements *)
          [] => NONE
          (* exactly one disagreement the between the heads / the args *)
        | [tpos] => SOME tpos
          (* the position of this combination is the disagreement *)
        | _ => SOME []
      end
    end
  | disagreement_tpos_of2 (t, u) = if t aconv u then NONE else SOME []

fun is_variable_headed t =
  let
    val (head, _) = strip_comb t
  in
    is_Var head
  end

(* FIXME: is this list complete? See Sign.logical_types *)
fun is_logical_symbol (Const (@{const_name "HOL.True"}, _)) = true
  | is_logical_symbol (Const (@{const_name "HOL.False"}, _)) = true
  | is_logical_symbol (Const (@{const_name "HOL.Not"}, _)) = true
  | is_logical_symbol (Const (@{const_name "HOL.disj"}, _)) = true
  | is_logical_symbol (Const (@{const_name "HOL.conj"}, _)) = true
  | is_logical_symbol (Const (@{const_name "HOL.implies"}, _)) = true
  | is_logical_symbol (Const (@{const_name "HOL.All"}, _)) = true
  | is_logical_symbol (Const (@{const_name "HOL.Ex"}, _)) = true
  | is_logical_symbol (Const (@{const_name "HOL.eq"}, _)) = true
  | is_logical_symbol _ = false

fun is_position_of_fully_applied_logical_symbol tpos term =
  let
    val head = subterm_at term tpos
  in
    if not (is_logical_symbol head) then false else
    (* \<top> and \<bottom> are always fully applied *)
    if head = @{term "True"} orelse head = @{term "False"} then true else
    (* now the logical symbol must have function type
    FIXME: check that \<top>, \<bottom> are the only atomic (?) logical symbols *)
    if tpos = [] then false else
    let
      val comb_pos = drop 1 tpos
      val comb = subterm_at term comb_pos
      val comb_typ = fastype_of comb
      fun is_comb (_ $ _) = true
        | is_comb _ = false
    in
      (* a logical symbol (except for \<top> and \<bottom>) is fully applied iff. it is the
      head of a combination with boolean type *)
      is_comb comb andalso @{typ "HOL.bool"} = comb_typ
    end 
  end

(* The arguments of f are in green position iff. f \<in> \<Sigma>\<setminus>{\<forall>, \<exists>}, where Free _ variables are taken to
be in \<Sigma>. *)
fun can_have_green_args (t as (Const _)) = not (is_quantifier t)
  | can_have_green_args (Free _) = true
  | can_have_green_args _ = false

fun green_tposs_of (t as (_$_)) =
      if can_have_green_args (head_of t)
        then
          let
            val tposs_of_head_and_args : tpos list list =
              map green_tposs_of (uncurry cons (strip_comb t))
            val tposs_of_comb =
              (* prepend term position in the combination *)
              map_index (fn (idx, tposs_of_subterm) => map (cons idx) tposs_of_subterm)
                tposs_of_head_and_args
          in
            (* drop the heads (sub)positions *)
            [] :: flat (drop 1 tposs_of_comb)
          end
      else [[]]
  | green_tposs_of _ = [[]] (* [\<epsilon>] *)

fun is_green_tpos [] _ = true
  | is_green_tpos (0 :: _) _ = false
  | is_green_tpos (i :: is) (t as (_$_)) =
      can_have_green_args (head_of t) andalso is_green_tpos is (subterm_at t [i])
  | is_green_tpos _ _ = false

fun head_tail_pair [] = error ""
  | head_tail_pair (x :: xs) = (x, xs)

fun map_at [] f t = f t
  | map_at (0 :: p) f (Abs(x,T,u)) = Abs(x,T,map_at p f u)
  | map_at (i :: p) f (t as (_$_)) =
      t |> strip_comb |> uncurry cons |> nth_map i (map_at p f) |> head_tail_pair |> list_comb
  | map_at _ _ _ = error ""

fun fold_non_greens_lvl (f : int -> term -> 'a -> 'a) (lvl : int) (t : term) (acc : 'a) =
  case t of
    Abs(_,_,u) => f (lvl + 1) u acc (* the abstraction itself is still green, it's body is not *)
  | (_$_) =>
      let
        val (head, args) = strip_comb t
      in
        if not (can_have_green_args head)
          (* the whole combination is still green, but it's head and all of the arguments aren't *)
          then fold (f lvl) (head :: args) acc
          (* all of the arguments are green (recurse) but the head isn't (pass to f) *)
          else fold (fold_non_greens_lvl f lvl) args acc |> f lvl head
      end
  | _ => acc (* leaves of the expression tree can be green, in which case there is no
  nongreen-subtree that can be viewed as a leaf. *)

(* We can fold, because nongreens never contain greens, so we can treat the nongreens as the leaves
of a tree. Or: a green position is always contained in another green position, as is the root so
they form a subtree starting at the root. The nongreen "leaves" are the ones 1 below the green
leaves. *)
fun fold_non_greens f = fold_non_greens_lvl (K f) 0

(* "A raw \<lambda>-term is ground if it is built without using type variables and contains no free term
variables" *)
fun is_not_ground t =
  let
    fun is_not_ground_type T =
      fold_atyps (fn U => fn acc => acc orelse is_TVar U) T false
    fun is_immediate_not_ground_term (Var _) = true
      | is_immediate_not_ground_term _ = false (* need to look further down *)
  in
    fold_term_types
      (fn t => fn T => fn acc =>
        acc orelse is_not_ground_type T orelse is_immediate_not_ground_term t)
      t
      false
  end

(* Overapproximation of fluid terms. Though not explicitely stated in the o\<lambda>Sup paper, Bound-headed
applications are not considered fluid (as in \<lambda>Sup and zipperposition) *)
fun might_be_fluid (t as (Abs _)) = is_not_ground t
  (* need to check if head of application is a variable *)
  | might_be_fluid (t as (_ $ _)) = (case strip_comb t of (Var _, _) => true | _ => false)
  | might_be_fluid _ = false

fun occurs_in x = exists_subterm (curry (op =) x)

(* FIXME: Check that this is the correct reading of Definition 23.

x occurs deeply in

y u\<^sub>n       iff. x occurs in any u\<^sub>i
Q (\<lambda>z.v)   iff. x occurs deeply in v
s u\<^sub>n       iff. x occurs deeply in s or x occurs deeply in any u\<^sub>i
(\<lambda>z.v)     iff. x occurs in v

Idea: recurse until condition is encountered which makes every occurence deep. *)
fun occurs_deeply_in x (t as (_ $ _)) =
  let
    val (head, args) = strip_comb t
  in
    case head of
      Var _ => exists (occurs_in x) args
    | _ =>
        if is_quantifier head andalso is_Abs (the_single args)
          then let val Abs(_,_,v) = the_single args in occurs_deeply_in x v end
          else exists (occurs_deeply_in x) (head :: args)
  end
  (* we know this abstraction will not be directly below a quantifier *)
  | occurs_deeply_in x (Abs(_,_,v)) = occurs_in x v
  (* in particular: x does not occur deeply in x *)
  | occurs_deeply_in _ _ = false

(* Q\<^sub>\<approx> normalizes, i.e. applies the rewrite rules
    \<forall> \<mapsto> \<lambda>y. y = (\<lambda>x. True)  (this is the polymorphic HOL.eq)
    \<exists> \<mapsto> \<lambda>y. y \<noteq> (\<lambda>x. False)
  where necessary:
    1. Quantifier has no arguments, or
    NOTE: the two cases below require \<beta>-reduction afterwards
    2. has an argument that is not a \<lambda>-expression (see questions below!), or
    3. has an argument \<lambda>x. v and x occurs free in a nongreen position of v. *)
fun norm_quantifier_poly_eq t =
  let
    (* \<beta>\<eta>-reduce first, to obtain situation where case 2 above is "logically meaningful" (??) for
    \<eta>-expansion (as is done in norm_beta_eta_qeta could always avoid case 2. *)
    val t = Envir.beta_eta_contract t
    fun bound_occurs_free_nongreen (Abs (a, _, s)) =
      (* Check if var referring to Bound 0 occurs in a nongreen position of s. *)
      if fold_non_greens_lvl
          (fn lvl => fn tm_nongreen => fn acc =>
            acc orelse loose_bvar1 (tm_nongreen, lvl)
          ) 0 s false
        then SOME a
        else NONE
      | bound_occurs_free_nongreen _ = error "not a \<lambda>-abstraction"
    fun rewrite_quantifier (t as Const(quantifier, _)) (x : string) =
      let
        val T = quantified_typ t
        val yT = T --> HOLogic.boolT
        val body = case quantifier of
            @{const_name HOL.All} =>
              HOLogic.mk_eq (Free("y", yT), Abs(x, T, @{term True}))
          | @{const_name HOL.Ex} =>
              HOLogic.mk_not
                (HOLogic.mk_eq (Free("y", yT), Abs(x, T, @{term False})))
          | _ => error "not a quantifier"
      in
        absfree ("y", T --> HOLogic.boolT) body
      end
      | rewrite_quantifier _ _ = error "not a constant"
  in
    case t of
      (* case 1: lone term w/o args *)
      Const _ => if is_quantifier t then rewrite_quantifier t Name.uu else t
      (* cases 2 & 3 *)
    | s $ u =>
        let val s' =
          if is_quantifier s then
            (* case 2 *)
            if not (is_Abs u) then
              rewrite_quantifier s Name.uu
            (* case 3 *)
            else case bound_occurs_free_nongreen u of
              SOME x => rewrite_quantifier s x
            | NONE => s
          else s
        in s' $ norm_quantifier_poly_eq u end
    | Abs(a, T, u) => Abs(a, T, norm_quantifier_poly_eq u)
    | _ => t
  end

(* Question: If \<eta>-expansion under quantifiers is done first then conversion to
Q\<^sub>\<approx> does nothing in case 2. above. But if conversion to Q\<^sub>\<approx> is done
first then some quantifiers disappear. Do we still want to do the former? If so it's probably for
good reasons. What are they?
Answer: "The Q\<^sub>\<approx>-normality of the initial clause set of a derivation will be a
precondition of the completeness theorem." *)

(* \<forall> (\<lambda>x.v) \<mapsto> \<lambda>y.y\<approx>(\<lambda>x.\<top>) *)

fun norm_beta_eta_env env = Envir.eta_contract o Envir.norm_term env

val norm_beta_eta = norm_beta_eta_env Envir.init

(* Q t \<mapsto> Q (\<lambda>x. t x) *)
fun ensure_lambda_under_q (t $ Abs (x, T, u)) = t $ Abs (x, T, ensure_lambda_under_q u)
  | ensure_lambda_under_q (t $ u) =
      if is_quantifier t
        then
          let val (T, _) = dest_funT (fastype_of u) in
            t $ Abs(Name.uu, T, incr_boundvars 1 (ensure_lambda_under_q u) $ Bound 0)
          end
        else ensure_lambda_under_q t $ ensure_lambda_under_q u
  | ensure_lambda_under_q t = t

(* apply substitution and normalize (compare Envir.beta_eta_contract) *)
fun norm_beta_eta_qeta_env env = ensure_lambda_under_q o norm_beta_eta_env env

(* applies \<beta> and \<eta> reduction and the rewrite rule
    Q t \<mapsto> Q (\<lambda>x. t x)
  i.e. \<eta>-expansion under quantifiers.
*)
val norm_beta_eta_qeta = norm_beta_eta_qeta_env Envir.init

end;