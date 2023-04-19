(*

general procedure:

1. Q\<^sub>\<approx> normalize
2. \<beta>\<eta>Q\<^sub>\<eta>-normalize
3. 

*)

open Jeha_Lang

signature JEHA =
sig
  (* outer clausification *)
  val outer_clausify : bool -> term -> clause -> clause list
  val simp_bool_outer_claus : clause -> cpos -> clause list
  val simp_rewrite_positive_lits : Proof.context -> clause * lpos -> clause * full_pos -> clause option
  val simp_rewrite_negative_lits : Proof.context -> clause * lpos -> clause * full_pos -> clause option
  val infer_eq_neq_outer_claus : clause -> cpos -> clause list
  val infer_sup : Proof.context -> (clause * (lpos * cpos)) -> (clause * full_pos) -> clause list
  val infer_eres : Proof.context -> (clause * cpos) -> clause list
  val forward_simplify : Proof.context -> clause list -> clause -> clause list
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

(* cartesian_product : 'a list -> 'b list -> ('a * 'b) list *)
fun cartesian_product [] _ = []
  | cartesian_product (x :: xs) ys = map (pair x) ys @ cartesian_product xs ys

fun seq_cartesian_product xs ys =
  case Seq.pull xs of
    SOME (x, xs) => Seq.append (Seq.map (pair x) ys) (seq_cartesian_product xs ys)
  | NONE => Seq.empty

fun map_some _ NONE = NONE
  | map_some f (SOME x) = SOME (f x)

(* oc function from the paper
logically: outer_clausify b s c = clauses of (if b then s else \<not>s) \<or> c
Distribute the first logical symbol (\<and>, \<or>, \<longrightarrow>) over the clause (removing prefix of negations
above and below) *)
(* FIXME: Implement as specified in PhD thesis. *)
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

fun prefix_Vars_TVars prefix =
  let 
    fun prefix_if_Var prefix (Var ((s, i),T)) = Var ((prefix ^ s, i), T)
      | prefix_if_Var _ u = u
    fun prefix_if_TVar prefix = map_type_tvar (fn ((s, i), S) => TVar ((prefix ^ s, i), S))
  in
    map_aterms (prefix_if_Var prefix) o map_types (prefix_if_TVar prefix)
  end

(** Simplification **)

(* Syntactic tautology deletion 1 (TD1) (Schulz) *)
fun contains_syntactic_equation [] = false
  | contains_syntactic_equation c =
      exists (fn (s, t, is_positive) => is_positive andalso s aconv t) c

(* Syntactic tautology deletion 2 (TD2) (Schulz) *)
fun contains_syntactic_complementaries [] = false
  | contains_syntactic_complementaries (l as (s, t, b) :: ls) =
      exists (curry aconv_lit (s, t, not b)) ls orelse contains_syntactic_complementaries ls

(* FIXME: implement semantic tautology deletion? *)

fun is_trivial c = contains_syntactic_equation c orelse contains_syntactic_complementaries c

(* Deletion of duplicated literals (DD) (Schulz) *)
fun simp_delete_duplicated_lits c =
  let
    fun impl_simp_delete_duplicated_lits [] = []
      | impl_simp_delete_duplicated_lits (l :: ls) = l :: filter (not o (curry aconv_lit l)) ls
    val c' = impl_simp_delete_duplicated_lits c
  in
    if length c' = length c
      then NONE
      else SOME c'
  end

(* Deletion of resolved literals (DR) (Schulz) *)
fun simp_delete_resolved_lits c =
  let
    val impl_simp_delete_resolved_lits =
      filter (fn (s, t, is_positive) => not is_positive andalso s aconv t)
    val c' = impl_simp_delete_resolved_lits c
  in
    if length c' = length c
      then NONE
      else SOME c'
  end

fun is_pos_unit [(_, _, true)] = true
  | is_pos_unit _ = false

(* Rewriting of positive (RP) or negative literals (RN) simplification (Schulz) *)
fun impl_simp_rewrite_lits positive ctxt (unit_clause, lp) (target_clause, j as (_, _, target_cp)) =
  (* check unit_clause *)
  if not (is_pos_unit unit_clause) then NONE else
  (* check that to be rewritten literal is indeed positive / negative *)
  if not (positive = #3 (nth target_clause target_cp)) then NONE else
  let
    (* make variables distinct *)
    val unit_clause = map (map_lit (prefix_Vars_TVars "L")) unit_clause
    val target_clause = map (map_lit (prefix_Vars_TVars "R")) target_clause
    val (from, to) = apply2 (term_at_lpos (the_single unit_clause)) (lp, swap_lpos lp) (* Schulz: (s, t) *)
    val target_term = subterm_at_full_pos target_clause j (* Schulz: u *)
    val unifiers = Unify.smash_unifiers (Context.Proof ctxt) [(from, target_term)] Envir.init
    fun build_conclusion unifier =
      let
        val (from, to) = apply2 (norm_beta_eta_env unifier) (from, to)
      in
        if SOME GREATER = Jeha_Order.kbo (from, to) then NONE else (* Schulz: \<sigma>(s) > \<sigma>(t) *)
        (* FIXME: understand and implement the restrictions on RP form Schulz's paper *)
        (* FIXME: check that the rewriting clause is smaller than the rewritten clause, see o\<lambda>Sup,
        p.25 *)
        let
          val rewritten_clause = map_at_full_pos j (K to) target_clause
        in
          writeln (Jeha_Common.pretty_tenv ctxt (Envir.term_env unifier));
          SOME (map (map_lit norm_beta_eta) rewritten_clause)
        end
      end
  in
    unifiers
    (* FIXME: print warning message when discarding unifiers? *)
    |> Seq.take 4
    |> Seq.map_filter build_conclusion
    |> Seq.pull
    |> map_some #1
  end

(* Rewriting of positive literals (RP) simplification (Schulz) *)
val simp_rewrite_positive_lits = impl_simp_rewrite_lits true

(* Rewriting of positive literals (RN) simplification (Schulz) *)
val simp_rewrite_negative_lits = impl_simp_rewrite_lits false

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
            map (map_lit (norm_beta_eta_env unifier)) (d' @ ct')
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
        map (map_lit (norm_beta_eta_env unifier)) c'
      end
  in
    if is_pos_eq
      then []
      else map build_conclusion unifiers
  end

(** Saturation Loop **)

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
fun forward_simplify ctxt active given_clause =
  let
    val active_units_all_orientations : (clause * lpos) list =
      cartesian_product (filter (fn c => length c = 1) active) [Left, Right]
    val rules = [simp_rewrite_negative_lits, simp_rewrite_positive_lits]
    fun first_successful_rewrite c =
      let
        val green_targets : (clause * full_pos) list = map (pair c) (green_full_poss_of c)
        val unit_target_pairs = cartesian_product active_units_all_orientations green_targets
        val rule_unit_target_triples = cartesian_product rules unit_target_pairs
        val first_rewrite =
          rule_unit_target_triples
          |> map_filter (fn (rule, (unit, target)) => rule ctxt unit target) 
          |> (fn cs => case cs of (c :: _) => SOME c | _ => NONE)
      in 
        first_rewrite
        (* if no rewrite has happened yet, try (DD) or (DR) *)
        |> (fn c' => if is_some c' then c' else simp_delete_duplicated_lits c) 
        |> (fn c' => if is_some c' then c' else simp_delete_resolved_lits c)
      end
    (* rewrite until not possible anymore *)
    (* FIXME: can this lead to a fixed-point (and not terminate)? *)
    fun full_rewrite c =
      case first_successful_rewrite c of
        SOME c' => full_rewrite c'
      | NONE => c
  in
    (* FIXME: Implement Positive simplify-reflect and Negative simplify-reflect *)
    (* FIXME: triviality check *)
    [full_rewrite given_clause]
  end
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
    case forward_simplify ctxt active given_clause of
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