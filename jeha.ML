(*

general procedure:

1. Q\<^sub>\<approx> normalize
2. \<beta>\<eta>Q\<^sub>\<eta>-normalize
3. 

*)

signature JEHA =
sig
  (* basics *)
  type literal = term * term * bool
  type clause = literal list
  datatype lpos = Left | Right
  type cpos = int
  val lit_of : term -> literal
  val map_lit : (term -> term) -> literal -> literal
  val clause_of : term -> clause
  val term_of_clause : clause -> term
  val is_quantifier : term -> bool
  val quantified_typ : term -> typ
  val strip_comb_fun_types_args : term -> term * typ list * term list
  val strip_comb_fun_types_args1 : typ list * term -> term * typ list * term list
  type tpos = int list
  type full_pos = tpos * lpos * cpos
  val green_full_poss_of : clause -> full_pos list
  val tposs_of : term -> tpos list
  val green_tposs_of : term -> tpos list
  val subterm_at_tpos : term -> tpos -> term
  val subterm_at_full_pos : clause -> full_pos -> term
  (* preprocessing *)
  val fold_non_greens_lvl : (int -> term -> 'a -> 'a) -> int -> term -> 'a -> 'a
  val fold_non_greens : (term -> 'a -> 'a) -> term -> 'a -> 'a
  val might_be_fluid : term -> bool
  val norm_quantifier_poly_eq : term -> term
  (* normalization *)
  val norm_beta_eta_qeta : term -> term
  (* outer clausification *)
  val outer_clausify : bool -> term -> clause -> clause list
  val simp_bool_outer_claus : clause -> cpos -> clause list
  val infer_eq_neq_outer_claus : clause -> cpos -> clause list
  val infer_sup : Proof.context -> (clause * (lpos * cpos)) -> (clause * full_pos) -> clause list
  val infer_eres : Proof.context -> (clause * cpos) -> clause list
  val simplify : Proof.context -> clause list -> clause -> clause list
  val infer_clauses : Proof.context -> clause list -> clause -> clause list
  (* *)
  structure Passive_Set : HEAP
  val passive_set_of_list : clause list -> Passive_Set.T
  type loopstate
  val given_clause_loop : Proof.context -> int -> Passive_Set.T -> clause list -> string
  val given_clause_step : Proof.context -> int -> Passive_Set.T -> clause list -> loopstate
  val refutable : Proof.context -> thm list -> thm -> bool
end

structure Jeha : JEHA =
struct

(* equation or disequation *)
type literal = term * term * bool;
(* disjunction of literals *)
type clause = literal list;
(* left or right side of an equational literal *)
datatype lpos = Left | Right;
(* position of literal in a clause *)
type cpos = int;

(* cartesian_product : 'a list -> 'b list -> ('a * 'b) list *)
fun cartesian_product [] _ = []
  | cartesian_product (x :: xs) ys = map (pair x) ys @ cartesian_product xs ys

fun swap_lit (s, t, b) = (t, s, b)

fun swap_lpos Left = Right
  | swap_lpos Right = Left

fun map_lit f (s, t, b) = (f s, f t, b)

(* Make equality between term and HOL Boolean, removing a prefix of negations from the term. *)
(* FIXME: is turning \<not>s \<approx> \<bottom> into s \<approx> \<top> okay? Should we use disequations instead of equations?
(see similar comment in dest_eq_bool_lit) *)
fun mk_lit_eq_bool (@{term Not} $ t) b = mk_lit_eq_bool t (not b)
  | mk_lit_eq_bool t b = (t, if b then @{term True} else @{term False}, true)

(* turn a boolean term into an equational literal *)
fun lit_of t =
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

(* converts boolean terms to lists of literals *)
fun clause_of t =
  if not (fastype_of t = @{typ bool})
    then error "can only turn boolean terms into clauses"
    else HOLogic.disjuncts t |> map lit_of

fun term_of_lit (s, t, b) = (if b then I else HOLogic.mk_not) (HOLogic.mk_eq (s, t))

fun term_of_clause [] = @{term False}
  | term_of_clause (c as (_ :: _)) =
      let
        val (x :: xs) = rev c
      in
        fold (curry HOLogic.mk_disj) (map term_of_lit xs) (term_of_lit x)
      end

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
    (* FIXME: Can we assume the output of fastype_of1 to be `[...] ---> ...` or can there be issues with
    type aliases etc.? *)
    val types = fastype_of1 (boundTs, f) |> binder_types |> take (length ts)
  in
    (f, types, ts)
  end

(* Translates Isabelle/HOL application (f $ u\<^sub>1) $ u\<^sub>2) \<dots> to o\<lambda>Sup application f \<open>\<tau>\<^sub>1, \<tau>\<^sub>2\<close> u\<^sub>1 u\<^sub>2 \<dots> with
explicit type args. *)
fun strip_comb_fun_types_args t = strip_comb_fun_types_args1 ([], t)

(* Term position, mostly for documentation / testing purposes. See long comment at bottom. *)
type tpos = int list;
type full_pos = tpos * lpos * cpos

fun cposs_of clause = 0 upto (length clause - 1)

fun lposs_of _ = [Left, Right]

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

(* t|\<^sub>p *)
fun subterm_at_tpos t [] = t
  | subterm_at_tpos (Abs(_,_,u)) (0 :: p) = subterm_at_tpos u p
  (* FIXME: when you forget to bind the t (via as) there is no warning and when
  you call the function from somewhere else, where a t has been declared it uses
  that. Scoping broken?? *)
  | subterm_at_tpos (t as (_$_)) (i :: p) = subterm_at_tpos (nth (uncurry cons (strip_comb t)) i) p
  | subterm_at_tpos _ _ = error ""

fun term_at_lpos (l, _, _) Left = l
  | term_at_lpos (_, r, _) Right = r

fun subterm_at_full_pos c (tp, lp, cp) = subterm_at_tpos (term_at_lpos (nth c cp) lp) tp

fun green_full_poss_of c =
  cposs_of c
  |> maps (fn cp => [Left, Right] |> map (fn lp => (subterm_at_full_pos c ([], lp, cp), lp, cp)))
  |> maps (fn (t, lp, cp) => map (fn tp => (tp, lp, cp)) (green_tposs_of t))

fun head_tail_pair [] = error ""
  | head_tail_pair (x :: xs) = (x, xs)

fun map_at_tpos [] f t = f t
  | map_at_tpos (0 :: p) f (Abs(x,T,u)) = Abs(x,T,map_at_tpos p f u)
  | map_at_tpos (i :: p) f (t as (_$_)) =
      t |> strip_comb |> uncurry cons |> nth_map i (map_at_tpos p f) |> head_tail_pair |> list_comb
  | map_at_tpos _ _ _ = error ""

fun map_at_lpos Left f (l, r, b) = (f l, r, b)
  | map_at_lpos Right f (l, r, b) = (l, f r, b)

val map_at_cpos = nth_map

fun map_at_full_pos (tp, lp, cp) f c = map_at_cpos cp (map_at_lpos lp (map_at_tpos tp f)) c

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
      fold_atyps (fn U => fn acc => acc orelse is_TFree U orelse is_TVar U) T false
    fun is_immediate_not_ground_term (Free _) = true
      | is_immediate_not_ground_term (Var _) = true
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
  | might_be_fluid (s $ t) = might_be_fluid s
  | might_be_fluid (Var _ $ _) = true
  | might_be_fluid _ = false

fun occurs_in_term x = exists_subterm (curry (op =) x)

(* FIXME: Check that this is the correct reading of Definition 23.

x occurs deeply in

y u\<^sub>n       iff. x occurs in any u\<^sub>i
Q (\<lambda>z.v)   iff. x occurs deeply in v
s u\<^sub>n       iff. x occurs deeply in s or x occurs deeply in any u\<^sub>i
(\<lambda>z.v)     iff. x occurs in v

Idea: recurse until condition is encountered which makes every occurence deep. *)
fun occurs_deeply_in_term x (t as (_ $ _)) =
  let
    val (head, args) = strip_comb t
  in
    case head of
      Var _ => exists (occurs_in_term x) args
    | _ =>
        if is_quantifier head andalso is_Abs (the_single args)
          then let val Abs(_,_,v) = the_single args in occurs_deeply_in_term x v end
          else exists (occurs_deeply_in_term x) (head :: args)
  end
  (* we know this abstraction will not be directly below a quantifier *)
  | occurs_deeply_in_term x (Abs(_,_,v)) = occurs_in_term x v
  (* in particular: x does not occur deeply in x *)
  | occurs_deeply_in_term _ _ = false

fun occurs_deeply_in_lit x (l, r, _) = occurs_deeply_in_term x l orelse occurs_deeply_in_term x r

fun occurs_deeply (x as (Var _)) = exists (occurs_deeply_in_lit x)
  | occurs_deeply _ = error "only Vars can occur deeply"

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


(* Q t \<mapsto> Q (\<lambda>x. t x) *)
fun ensure_lambda_under_q (t $ Abs (x, T, u)) = t $ Abs (x, T, ensure_lambda_under_q u)
  | ensure_lambda_under_q (t $ u) =
      if is_quantifier t
        then
          let val (T, _) = dest_funT (fastype_of u) in
            Abs(Name.uu, T, incr_boundvars 1 (ensure_lambda_under_q u) $ Bound 0)
          end
        else ensure_lambda_under_q t $ ensure_lambda_under_q u
  | ensure_lambda_under_q t = t

(* apply substitution and normalize (compare Envir.beta_eta_contract) *)
fun norm_beta_eta_qeta_env env = ensure_lambda_under_q o Envir.eta_contract o Envir.norm_term env

(* applies \<beta> and \<eta> reduction and the rewrite rule
    Q t \<mapsto> Q (\<lambda>x. t x)
  i.e. \<eta>-expansion under quantifiers.
*)
val norm_beta_eta_qeta = norm_beta_eta_qeta_env Envir.init

(* oc function from the paper
logically: outer_clausify b s c = clauses of (if b then s else \<not>s) \<or> c
Distribute the first logical symbol (\<and>, \<or>, \<longrightarrow>) over the clause (removing prefix of negations
above and below) *)
(* FIXME: Making HO Sup work p.7 says: never simplify \<longleftrightarrow>. What does this mean concretely? (Isabelle
represents \<longleftrightarrow> as HOL.eq) *)
fun outer_clausify b (@{term Not} $ s) c = outer_clausify (not b) s c
  | outer_clausify b (Const (@{const_name HOL.disj}, _) $ s $ t) c =
    if b
      then [mk_lit_eq_bool s b :: mk_lit_eq_bool t b :: c]
      else [mk_lit_eq_bool s b :: c, mk_lit_eq_bool t b :: c]
  | outer_clausify b (Const (@{const_name HOL.conj}, _) $ s $ t) c =
    if b
      then [mk_lit_eq_bool s b :: c, mk_lit_eq_bool t b :: c]
      else [mk_lit_eq_bool s b :: mk_lit_eq_bool t b :: c]
  | outer_clausify b (Const (@{const_name HOL.implies}, _) $ s $ t) c =
      (* rewrite as disjunction, additional not will be removed in mk_lit_eq_bool *)
      outer_clausify b (HOLogic.mk_disj (HOLogic.mk_not s, t)) c
  | outer_clausify b s c = [mk_lit_eq_bool s b :: c]

(*** Rules ***)
(* rule implementation checklist:
  * conditions checked?
  * requires normalization?
  * 
*)

(** Clausification **)

fun is_boolean_const t = t = @{term True} orelse t = @{term False}

fun ml_bool_of @{term True} = true
  | ml_bool_of @{term False} = false
  | ml_bool_of _ = error "term is not HOL.True or HOL.False"

fun is_eq_bool_lit (s, t, true) = exists is_boolean_const [s, t]
    (* FIXME: Maybe accept boolean disequations? (by turning them into equations) *)
  | is_eq_bool_lit _ = false

fun dest_eq_bool_lit (s, t, true) =
  if is_boolean_const t
    then (s, t)
  else if is_boolean_const s
    then (t, s)
  else error "neither is HOL.True or HOL.False"
  (* FIXME: allow disequations? (see similar comment above mk_lit_eq_bool) *)
  | dest_eq_bool_lit _ = error "disequation"

(* PosOuterClaus and NegOuterClaus simplficiations *)
fun simp_bool_outer_claus c i =
  let
    val (s, b) = nth c i |> dest_eq_bool_lit ||> ml_bool_of
    val c' = nth_drop i c
  in
    outer_clausify b s c'
  end

fun find_simp_bool_outer_clause c = error "find_simp_bool_outer_clause unimplemented"

(* EqOuterClaus and NeqOuterClaus inferences *)
fun infer_eq_neq_outer_claus c i =
  let
    val (s, t, b) = nth c i
  in
    if not (fastype_of s = @{typ bool} andalso fastype_of t = @{typ bool})
      then error "not boolean equation"
    else if b
      then (* EqOuterClaus *)
        [ mk_lit_eq_bool s false :: mk_lit_eq_bool t true :: c
        , mk_lit_eq_bool s true :: mk_lit_eq_bool t false :: c
        ]
      else (* NeqOuterClaus *)
        [ mk_lit_eq_bool s false :: mk_lit_eq_bool t false :: c
        , mk_lit_eq_bool s true :: mk_lit_eq_bool t true :: c
        ]
  end

fun prefix_Vars_TVars prefix =
  let 
    fun prefix_if_Var prefix (Var ((s, i),T)) = Var ((prefix ^ s, i), T)
      | prefix_if_Var _ u = u
    fun prefix_if_TVar prefix = map_type_tvar (fn ((s, i), S) => TVar ((prefix ^ s, i), S))
  in
    map_aterms (prefix_if_Var prefix) o map_types (prefix_if_TVar prefix)
  end

(* Sup inference *)
fun infer_sup ctxt (d, i as (lp, cp)) (c, j) =
  let
    (* FIXME: better renaming strategy: collect Vars from one term in a Vars structure
    (term_item.ML), traverse the other creating an environment mapping names already used to fresh
    names
    ALSO: Only make t and u (and compose environments afterwards? Envir.merge?)
    OR: try to use Envir.empty max_idx (augment clauses with max_idx?) and Envir.genvar
    SEE: COMP_INCR maybe?
    NOTE: how to handle TVars? *)
    val d = map (map_lit (prefix_Vars_TVars "L")) d
    val c = map (map_lit (prefix_Vars_TVars "R")) c
    (* FIXME: pick the correct one (t or t') *)
    val (_, _, is_pos_eq) = nth d cp
    val t = subterm_at_full_pos d ([], lp, cp)
    val t' = subterm_at_full_pos d ([], swap_lpos lp, cp)
    val u = subterm_at_full_pos c j
  in
    if not is_pos_eq
      then []
    else if might_be_fluid u
      then error "u might be fluid"
    else if is_Var u andalso occurs_deeply u c
      then error "u occurs deeply in c"
    else
      (* FIXME: Is smash_unifiers the one we want? How lossy is this? *)
      (* FIXME: Later, try to keep around flex-flex pairs for a while? *)
      let
        val unifiers = Unify.smash_unifiers (Context.Proof ctxt) [(t, u)] Envir.init
        (* FIXME: print warning message when discarding unifiers *)
        val (unifiers, _) = Seq.chop 4 unifiers
        fun build_conclusion unifier =
          let
            val d' = nth_drop cp d
            val ct' = map_at_full_pos j (K t') c
          in
            writeln (Jeha_Common.pretty_tenv ctxt (Envir.term_env unifier));
            map (map_lit (norm_beta_eta_qeta_env unifier)) (d' @ ct')
          end
      in
        map build_conclusion unifiers
      end
  end

(* ERes inference *)
fun infer_eres (ctxt : Proof.context) ((c, cp) : (clause * cpos)) =
  let
    val (u, u', is_pos_eq) = nth c cp
    val unifiers = Unify.smash_unifiers (Context.Proof ctxt) [(u, u')] Envir.init
    (* FIXME: print warning message when discarding unifiers *)
    val (unifiers, _) = Seq.chop 4 unifiers
    fun build_conclusion unifier =
      let
        val c' = nth_drop cp c
      in
        writeln (Jeha_Common.pretty_tenv ctxt (Envir.term_env unifier));
        map (map_lit (norm_beta_eta_qeta_env unifier)) c'
      end
  in
    if is_pos_eq
      then []
      else map build_conclusion unifiers
  end

(* Passive_Set *)

fun size_of_clause clause =
  fold (fn (l, r, _) => fn acc => acc + size_of_term l + size_of_term r) clause 0

val size_ord = make_ord (fn (c, d) => size_of_clause c <= size_of_clause d)

(* FIXME: Heap recomputes size (maybe `type elem = int * clause`?) *)
structure Passive_Set = Heap(type elem = clause val ord = size_ord)

fun list_of_passive_set passive =
  if Passive_Set.is_empty passive
    then []
    else Passive_Set.min_elem passive ||> list_of_passive_set |> uncurry cons

fun passive_set_of_list clauses = fold Passive_Set.insert clauses Passive_Set.empty

fun add_new_clauses passive clauses = fold Passive_Set.insert clauses passive

fun select_given_clause cs = Passive_Set.min_elem cs

(* FIXME: do simplification *)
(* FIXME: make sure to include given_clause itself in simplificatons unless it's redundant *)
fun simplify ctxt active given_clause =
  if exists (curry (op =) given_clause) active then [] else [given_clause]
  (* let
    val idxs = find_simp_bool_outer_clause given_clause
    val outer_clausified = flat (map (simp_bool_outer_claus given_clause) idxs)
  in
    outer_clausified
  end *)

fun infer_clauses ctxt active given_clause =
  let
    (* the equality literals that are being eliminated *)
    val eqs_given : (clause * (lpos * cpos)) list =
      map (pair given_clause) (cartesian_product [Left, Right] (cposs_of given_clause))
    val eqs_active : (clause * (lpos * cpos)) list =
      maps (fn c => map (pair c) (cartesian_product [Left, Right] (cposs_of c))) active
    (* what we're superposing into *)
    val targets_given : (clause * full_pos) list =
      map (pair given_clause) (green_full_poss_of given_clause)
    val targets_active : (clause * full_pos) list =
      maps (fn c => map (pair c) (green_full_poss_of c)) active
    val eq_target_pairs =
      cartesian_product eqs_given targets_active @ cartesian_product eqs_active targets_given
  in
    maps (uncurry (infer_sup ctxt)) eq_target_pairs
    (* ERes has already been performed for the active clauses *)
    @ maps (infer_eres ctxt) (map (pair given_clause) (0 upto (length given_clause - 1)))
  end

(* Question: Are clauses and literals multisets? *)

datatype loopstate = Timeout | Unsat | Next of Passive_Set.T * clause list

fun given_clause_step ctxt countdown passive active =
  if countdown <= 0 then Timeout else
  let
    (* FIXME: return MAYBE_SAT (because of incompleteness) if passive set is empty (i.e. no
    inferences are possible and empty clause has not been derived). Later: no non-redundant
    inferences *)
    val (given_clause, passive) = select_given_clause passive
    (* tracing *)
    fun trace_msg_clauses msg clauses =
      Jeha_Common.trace_msg ctxt
        (fn () => msg ^ Jeha_Common.pretty_terms ctxt (map term_of_clause clauses))
    val _ = trace_msg_clauses "passive: " (list_of_passive_set passive)
    val _ = trace_msg_clauses "active: " active
    val _ = trace_msg_clauses "given_clause " [given_clause]
    (* simplify given_clause with active set *)
  in
    case simplify ctxt active given_clause of
      (* given_clause redundant w.r.t. active set *)
      [] => Next (passive, active)
      (* select first simplification as given_clause *)
    | given_clause :: simplifications => 
      (* if given_clause simplifies to (or is) [] then UNSAT *)
      if exists (curry (op =) []) (given_clause :: simplifications)
        then Unsat
        else
          let
            (* following zipperposition (src/prover/saturate.ml) add all simplifications except one
            (the current given_clause) to the passive set *)
            val passive = add_new_clauses passive simplifications
            (* perform all possible inferences between given_clause and active set *)
            val new_clauses = infer_clauses ctxt active given_clause
            (* add inferred clauses to passive set *)
            val passive = add_new_clauses passive new_clauses
          in
            (* add given_clause to active and continue *)
            Next (passive, (given_clause :: active))
          end
  end

fun given_clause_loop ctxt countdown passive active =
  case given_clause_step ctxt countdown passive active of
    Timeout => "TIMEOUT"
  | Unsat => "UNSAT"
  | Next (passive, active) => given_clause_loop ctxt (countdown - 1) passive active

fun refutable ctxt axioms conjecture =
  let
    val _ = Jeha_Common.trace_msg ctxt
      (fn () => "conjecture: " ^ Jeha_Common.pretty_term ctxt (Thm.prop_of conjecture))
    val axioms = map (Object_Logic.atomize_term ctxt o Thm.prop_of) axioms
    val neg_conjecture = HOLogic.mk_not (Object_Logic.atomize_term ctxt (Thm.prop_of conjecture))
    val clauses = map clause_of (neg_conjecture :: axioms)
    val _ = Jeha_Common.trace_msg ctxt (fn () => "clauses: " ^ Jeha_Common.pretty_terms (Jeha_Common.verbose_of ctxt) (map term_of_clause clauses))
    val result = given_clause_loop ctxt 20 (passive_set_of_list clauses) []
  in
    if result = "UNSAT" then true else false
  end

(*
Question:

f x y         f(x, y)

  $              f
 /|\      or    / \    ?
f x y          x   y
(HO)            (FO)

  / \
 $
/ \
f  x

x is green. What about f itself?

green part:
  $
  |\
  x y

nongreen leaves:
   
 /  
f    

FIXME: f x is a subterm

Counter argument:
o\<lambda>Sup paper, below Definition 6:
  "[...] or has an argument of the form \<lambda>x. v such that x occurs free in a nongreen position of v."

consider v = f x y

If the term f x is in a nongreen position f x y then x occurs in a nongreen position subterm of v. x also
occurs in a green position of v.

But if we take v = f y x then x occurs only in green positions of v.

If however f x is not a subterm of f x y at all, this ambiguity disappears.

Proposed Definitions:
* variadic application (/combination) with function as it's first child and arguments as the rest
* term positions: standard definition of position in a tree
* green positions as in paper
* nongreen positions are all the other positions

Observation:
* The whole tree is green.
* Every suffix of a green position is a green position.
=> The green positions span a subtree starting at the root.




*)
end;