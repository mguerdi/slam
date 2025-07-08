(* Functions in this module can
  1. silently break invariants (typically `origin`)
  2. break invariants by invalidating them (e.g. replacing maxidx by ~1, see NOTE: ...)
  3. don't break any invariants
It might be worth it to clearly separate them. Alternatively use option 2 everywhere in favour of 1.
But there needs to be some set of low level primitives which use option 1 because otherwise we can
never fix one invariant without breaking another. We could keep these low level primitives private
and only expose functions of the second and third kind to users?
*)

signature JCLAUSE =
sig
  (*
  type cpos = int
  type full_pos = JTerm.tpos * JLit.lpos * cpos
  *)
  exception NOBOOL of string * term * typ
  include JCLAUSE_POS
  type T
  val literals : T -> JLit.T list
  val id : T -> int
  val maxidx : T -> int
  val maxidx_of2 : T * T -> int
  val set_maxidx : int -> T -> T
  val set_origin : int Jeha_Log.inference -> T -> T
  val origin : T -> int Jeha_Log.inference
  val lit_at : cpos -> T -> JLit.T
  (* law: JLit.term_of (lit_at cp c) = JTerm.subterm_at (as_tpos c) (term_of c) *)
  val as_tpos : int -> cpos -> JTerm.tpos
  val dummy : JLit.T list -> T
  val refresh_id : unit -> T -> T
  val add_literal : Proof.context -> JLit.T -> T -> T
  val combine : Proof.context -> T -> T -> T
  val delete_lit_at : Proof.context -> cpos -> T -> T
  val delete_lits_at : Proof.context -> cpos list -> T -> T
  val filter_out_lits : Proof.context -> (JLit.T -> bool) -> T -> T
  val length : T -> int
  val of_term : Proof.context -> term * int -> T
  val term_of : T -> term
  val pretty_clause : Proof.context -> T -> string
  val pretty_clause' : Proof.context -> T -> Pretty.T
  val pretty_clauses : Proof.context -> T list -> string
  val pretty_clauses' : Proof.context -> T list -> Pretty.T
  val pretty_subterm : Proof.context -> T -> full_pos -> string
  val pretty_subterm' : Proof.context -> T -> full_pos -> Pretty.T
  val pretty_lit : Proof.context -> T -> cpos -> string
  val pretty_lit' : Proof.context -> T -> cpos -> Pretty.T
  val pretty_oriented : Proof.context -> T -> JLit.lpos * cpos -> string
  val pretty_oriented' : Proof.context -> T -> JLit.lpos * cpos -> Pretty.T
  val cposs_of : T -> cpos list
  val green_full_poss_of : T -> full_pos list
  val map_at_cpos : cpos -> (JLit.T -> JLit.T) -> T -> T (* NOTE: invalidates maxidx, selected *)
  val map_at_full_pos : full_pos -> (term -> term) -> T -> T (* NOTE: invalidates maxidx, selected *)
  val map_literals : (JLit.T list -> JLit.T list) -> T -> T (* NOTE: invalidates maxidx, selected *)
  val subterm_at_full_pos : T -> full_pos -> term
  (* law: subterm_at_full_pos fp [\<dots>, (s, t, b), \<dots>]
            = JTerm.subterm_at (full_pos_as_tpos b fp) (term_of [\<dots>, (s, t, b), \<dots>]) *)
  val full_pos_as_tpos : int -> bool -> full_pos -> JTerm.tpos
  val occurs_deeply : term -> T -> bool
  val norm_beta_eta_qeta_env : Proof.context -> Envir.env -> T -> T
  val norm_beta_eta_qeta : Proof.context -> T -> T
  val norm_negative_predicate_literals : Proof.context -> T -> T
  val incr_indexes : int -> T -> T
  val kbo : T * T -> Jeha_Order.partial_order
  val is_eligible_cpos : T -> cpos -> bool
  val is_eligible_full_pos : T -> full_pos -> bool
  val is_position_of_fully_applied_logical_symbol : full_pos -> T -> bool
  val is_false : T -> bool
  val is_unit : T -> bool
  val is_positive_unit : T -> bool
  val the_unit_lit : T -> JLit.T
  val orient_unit : JLit.lpos -> T -> term * term * bool
  val maxidx_of_literal_list : JLit.T list -> int
  (* literal selection *)
  val selected : T -> int list
  type literal_selection_function = Proof.context -> JLit.T list -> int list
  val select_none : literal_selection_function
  val select_all_neg_lit : literal_selection_function
  val select_first_maximal_neg_lit : literal_selection_function
  val recompute_selected : Proof.context -> T -> T
  (* Debuggging *)
  val is_eligible_tpos : term -> JTerm.tpos -> bool
end;

structure JClause : JCLAUSE =
struct

exception NOBOOL of string * term * typ

open JClause_Pos

type T =
  { literals: JLit.T list
  , id : int
  , maxidx : int
  , origin: int Jeha_Log.inference
  , selected: cpos list
  (* , normalized: bool *)
  }

type cpos = int
type full_pos = JTerm.tpos * JLit.lpos * cpos

val literals = #literals

val id = #id

val maxidx = #maxidx

val maxidx_of2 = Int.max o apply2 maxidx

val empty = { literals = [], id = ~1, maxidx = ~1, origin = Jeha_Log.Invalid, selected = [] }

(* NOTE: invalidates maxidx and selection *)
fun map_literals f { literals, id, maxidx, origin, selected } =
  { literals = f literals, id = id, maxidx = ~1, origin = origin, selected = [~1] }

fun unsafe_map_literals f { literals, id, maxidx, origin, selected } =
  { literals = f literals, id = id, maxidx = maxidx, origin = origin, selected = selected }

fun lit_at cp clause = nth (literals clause) cp

fun dummy literals =
  map_literals (K literals) empty

fun map_id f { literals, id, maxidx, origin, selected } =
  { literals = literals, id = f id, maxidx = maxidx, origin = origin, selected = selected }

fun refresh_id _ = map_id (K (JClause_Id.new ()))

fun maxidx_of_literal_list ls =
  fold (fn l => fn maxidx => Int.max (JLit.maxidx_of l, maxidx)) ls ~1

fun map_maxidx f { literals, id, maxidx, origin, selected } =
  { literals = literals, id = id, maxidx = f maxidx, origin = origin, selected = selected }

fun set_maxidx maxidx = map_maxidx (K maxidx)

fun set_origin origin { literals, id, maxidx, selected, ... } =
  { literals = literals, id = id, maxidx = maxidx, selected = selected, origin = origin }

fun origin { origin, ... } = origin

(* FIXME: use this for testing *)
fun recalculate_maxidx clause =
  set_maxidx (maxidx_of_literal_list (literals clause)) clause

(* literal selection functions *)

fun map_selected f { literals, id, maxidx, origin, selected } =
  { literals = literals, id = id, maxidx = maxidx, origin = origin, selected = f selected }

fun set_selected selected = map_selected (K selected)

fun selected { selected, ... } = case selected of
  [~1] => error "selected has been invalidated"
  | _ => selected

type literal_selection_function = Proof.context -> JLit.T list -> int list

fun select_none _ _ = []

fun is_selectable ctxt lit =
  JLit.is_negative_or_negativoid_cfg ctxt lit
    andalso (Config.get ctxt Jeha_Common.select_flex_sided orelse not (JLit.is_flex_sided lit))

fun select_all_neg_lit (ctxt : Proof.context) lits =
  lits
  |> map_index I
  |> map_filter (fn (cpos, lit) => if is_selectable ctxt lit then SOME cpos else NONE)

fun select_first_neg_lit ctxt lits =
  lits
  |> map_index I
  |> get_first (fn (cpos, lit) => if is_selectable ctxt lit then SOME cpos else NONE)
  |> the_list

fun select_first_maximal_neg_lit ctxt lits =
  let
    val neg_lits_cposs =
      lits
      |> map_index I
      (* FIXME: maybe the blocker disallowing for selection of literals with a variable-headed side
      is really important? *)
      |> filter (fn (cpos, lit) => is_selectable ctxt lit)
    val max_neg_lits = Jeha_Order.idxs_of_maximal_elements (JLit.kbo o apply2 #2) neg_lits_cposs
  in
    case max_neg_lits of
      (* index into neg_lits_cposs! *)
      (idx, _)::_ => [#1 (nth neg_lits_cposs idx)]
    | _ => []
  end

val literal_selection_functions =
  ["select_none", "select_all_neg_lit", "select_first_neg_lit", "select_first_maximal_neg_lit"]

fun literal_selection_function_from_name name = case name of
  "select_none" => select_none
  | "select_all_neg_lit" => select_all_neg_lit
  | "select_first_neg_lit" => select_first_neg_lit
  | "select_first_maximal_neg_lit" => select_first_maximal_neg_lit
  | name =>
    if member (op=) literal_selection_functions name
      then error ("BUG: JClause.literal_selection_functions and " ^
       "JClause.literal_selection_function_from_name are out-of-sync.")
      else
        error (
          "literal_selection_function_from_name: unknown selection function \"" ^ name ^ "\"\n" ^
          "possible values:\n" ^
          " * " ^ space_implode "\n * " literal_selection_functions
        )

fun get_literal_selection_function ctxt =
  Config.get ctxt Jeha_Common.literal_selection_function
  |> literal_selection_function_from_name
  |> (fn f => f ctxt)

(* NOTE: This needs to be done every time before checking eligibility and also after normalizing
negative predicate literals (s \<noteq> \<top> \<mapsto> s = \<bottom>) before the clause is "finalized". *)
fun recompute_selected ctxt clause =
  set_selected
    (get_literal_selection_function ctxt (literals clause))
    clause

fun add_literal ctxt l clause =
  clause
  |> map_literals (fn lits => lits @ [l])
  |> refresh_id ()
  |> set_maxidx (Int.max (maxidx clause, JLit.maxidx_of l))

fun combine ctxt c d =
  map_literals (curry (op @) (literals c)) d
  |> refresh_id ()
  |> set_maxidx (maxidx_of2 (c, d))

fun delete_lit_at ctxt cp clause =
  clause
  |> map_literals (nth_drop cp)
  |> refresh_id ()
  |> set_maxidx (maxidx clause)

fun delete_lits_at ctxt cps clause =
  let
    val sorted = sort (rev_order o int_ord) cps
  in
    fold (delete_lit_at ctxt) sorted clause
  end

fun filter_out_lits ctxt f clause =
  clause
  |> map_literals (filter_out f)
  |> set_maxidx (maxidx clause)

val length = List.length o literals

fun term_of { literals = [], ... } = @{term False}
  | term_of { literals = (c as (_ :: _)), ... } =
      let
        val (x :: xs) = rev c
      in
        fold (curry HOLogic.mk_disj) (map JLit.term_of xs) (JLit.term_of x)
      end

fun pretty_clause' ctxt c =
  let
    val origin = #origin c
    val premises = case origin of
      Jeha_Log.Invalid => "[Invalid]"
    | _ => @{make_string} (Jeha_Log.premises origin)
  in
    Pretty.block
      [ Pretty.str (@{make_string} (#id c) ^ ":")
      , Syntax.pretty_term ctxt (term_of c)
      , Pretty.str (" (" ^ (Jeha_Log.name_of origin) ^ " " ^ premises ^ ")")
      ]
  end

val pretty_clause = Pretty.string_of oo pretty_clause'

fun pretty_clauses' ctxt cs =
  cs
  |> map (pretty_clause' ctxt)
  |> Pretty.commas
  |> Pretty.block

val pretty_clauses = Pretty.string_of oo pretty_clauses'

(* Dependeing on clause length:
Length 0: error (the empty clause has no literals)
Length 1: [] (the root is the literal)
Length 2:
     /\
    0  1
  which have subterm positions [1] and [2].
Recursion via this invariant:
  * add another /\ on the top left
  * increment indices by 1
  * prefix term positions by 2
    /\
   0 /\
    1  2  (formerly 0, 1, with subterm positions [1], [2], now [2, 1], [2, 2])
*)
fun as_tpos 1 0 = []
  | as_tpos 2 0 = [1]
  | as_tpos 2 1 = [2]
  | as_tpos len cp =
      if cp >= len then
        error ("as_tpos: cp " ^ @{make_string} cp ^ " is not a valid index into a clause of length "
          ^ @{make_string} len)
      else
        2::as_tpos (len - 1) (cp - 1)

fun full_pos_as_tpos clause_len positive_lit (tp, lp, cp) =
  as_tpos clause_len cp @ JLit.as_tpos positive_lit lp @ tp

fun impl_pretty_subterm' ctxt c as_tp =
  let
    val as_term = term_of c
  in
    JTerm.pretty_subterm' ctxt as_term as_tp
  end

fun pretty_subterm' ctxt c (tp, lp, cp) =
  let
    val fp_as_tp = full_pos_as_tpos (length c) (JLit.is_positive (lit_at cp c)) (tp, lp, cp)
  in
    impl_pretty_subterm' ctxt c fp_as_tp
  end

val pretty_subterm = Pretty.string_of ooo pretty_subterm'

fun pretty_lit' ctxt c cp = impl_pretty_subterm' ctxt c (as_tpos (length c) cp)

val pretty_lit = Pretty.string_of ooo pretty_lit'

(* lp points to the lhs of the conditional rewrite rules conclusion *)
fun pretty_oriented' ctxt c (lp, cp) =
  let
    fun term_of_lit (cp', lit) =
      if cp = cp' then JLit.as_oriented_for_pretty lit lp else JLit.term_of lit
    fun term_of_lits [] = @{term False}
      | term_of_lits lits =
          let
            val (x :: xs) = rev lits
          in
            fold
              (curry HOLogic.mk_disj)
              (map_index term_of_lit xs)
              (term_of_lit (List.length lits - 1, x))
          end
    val t = term_of_lits (literals c)
  in
    Jeha_Common.pretty_term' ctxt (term_of_lits (literals c))
  end

val pretty_oriented = Pretty.string_of ooo pretty_oriented'

fun cposs_of c = 0 upto (length c - 1)

fun subterm_at_full_pos { literals, ... } (tp, lp, cp) = JTerm.subterm_at (JLit.term_at_lpos (nth literals cp) lp) tp

fun green_full_poss_of c =
  cposs_of c
  |> maps (fn cp => [JLit.Left, JLit.Right] |> map (fn lp => (subterm_at_full_pos c ([], lp, cp), lp, cp)))
  |> maps (fn (t, lp, cp) => map (fn tp => (tp, lp, cp)) (JTerm.green_tposs_of t))

(* NOTE: invalidates maxidx and selection *)
fun map_at_cpos i f clause =
  clause
  |> map_literals (nth_map i f)

(* NOTE: invalidates maxidx and selection *)
fun map_at_full_pos (tp, lp, cp) f c = map_at_cpos cp (JLit.map_at_lpos lp (JTerm.map_at tp f)) c

fun occurs_deeply (x as (Var _)) { literals, ... } = exists (JLit.occurs_deeply_in x) literals
  | occurs_deeply _ _ = error "only Vars can occur deeply"

fun norm_beta_eta_qeta_env ctxt env clause =
  (* if Envir.maxidx_of env < maxidx clause
    (* this indicates something went wrong *)
    then error "maxidx of env should be greater or equal to maxidx of clause"
    else *)
      clause
      |> map_literals (map (JLit.map (JTerm.norm_beta_eta_qeta_env env)))
      |> set_maxidx (Int.max (Envir.maxidx_of env, maxidx clause))

fun norm_beta_eta_qeta ctxt clause =
  norm_beta_eta_qeta_env ctxt (Envir.empty (maxidx clause)) clause

fun norm_negative_predicate_literals ctxt clause =
  let
    val maxidx = maxidx clause
    val selected = #selected clause
  in
    clause
    |> map_literals (map (JLit.norm_negative_pred ctxt))
    |> set_maxidx maxidx
    |> set_selected selected
  end

(* converts boolean terms to lists of literals *)
fun of_term ctxt (t, id) =
  if not (fastype_of t = @{typ bool})
    then raise (NOBOOL ("can only turn boolean terms into clauses", t, (fastype_of t)))
    else
      empty
      |> map_id (K id)
      |> map_literals (K (HOLogic.disjuncts t |> map JLit.of_term))
      |> recalculate_maxidx
      |> norm_beta_eta_qeta ctxt
      |> norm_negative_predicate_literals ctxt
      |> recompute_selected ctxt

fun incr_indexes increment clause =
  clause
  |> map_literals (map (JLit.map (Logic.incr_indexes ([], increment))))
  |> set_maxidx (increment + maxidx clause)

val kbo = Jeha_Order.mk_multiset_order_of_strict JLit.kbo o apply2 literals

(* Eligibility without selection functions:
Definition 22 (Eligibility) A literal L is (strictly) \<ge>-eligible w.r.t. a substitution \<sigma> in C for
some relation \<ge> if L\<sigma> is (strictly) \<ge>-maximal in C\<sigma>.
The \<ge>-eligible positions of clause C w.r.t a substitution \<sigma> are inductively defined as follows:
(E2) If a literal L = s \<doteq> t with \<not> (s\<sigma> \<le> t\<sigma>) is either \<ge>-eligible and negative or strictly
      \<ge>-eligible and positive, then L.s.\<epsilon> is \<ge>-eligible.
(E2.1) L.s.\<epsilon> if L = (s = t) with \<not> (s\<sigma> \<le> t\<sigma>) is strictly \<ge>-eligible.
(E2.2) L.s.\<epsilon> if L = (s \<noteq> t) with \<not> (s\<sigma> \<le> t\<sigma>) is \<ge>-eligible.
(E3) ...
(E4) ...
*)

(* unfortunately we can't define these functions in JTerm because they depend on Jeha_Order
FIXME: create BASIC_JTERM, have Jeha_Order depend on that, then use include / open in JTERM / JTerm
to define JTerm.kbo etc. *)

fun is_eligible_tpos_in_eq (Const (@{const_name "HOL.eq"}, _) $ s $ t) (i :: tpos) =
  let 
    val s_t_comp = Jeha_KBO.ord (s, t)
  in
    not (s_t_comp = SOME EQUAL) andalso
      case i of
        1 => not (s_t_comp = SOME LESS)
      | 2 => not (s_t_comp = SOME GREATER)
      | _ => error "non green position in is_eligible_tpos_in_eq"
  end

fun is_eligible_tpos _ [] = true
  (* subterms of fully applied equalities *)
  (* FIXME: what about partially applied equalities? see pdf comment in o\<lambda>Sup Definition 22 *)
  | is_eligible_tpos
      (t as ((Const (@{const_name "HOL.eq"}, _)) $ _ $ _))
      (tpos as (_ :: _))
    = is_eligible_tpos_in_eq t tpos
  (* general case *)
  | is_eligible_tpos t (i :: tpos) =
      if not (JTerm.is_green_tpos [i] t) then error "non green position in is_eligible_tpos" else
      is_eligible_tpos (JTerm.subterm_at t [i]) tpos

(* NOTE: This is not eligibility of literals as defined in \<lambda>oSup Def 22. but
rather, it anticipates the latter part of Def. 22 (E2), i.e.
  cpos of a positive literal is eligible if the literal is strictly Def22-eligible
  cpos of a negative literal is eligible if the literal is          Def22-eligible
In practice the o\<lambda>Sup paper only ever asks for strict eligibility of positive literals
(/ eligibility of negative literals) so we don't need the generality of Def. 22 *)
fun is_eligible_cpos c cpos =
  let
    val literals = literals c
    val literal = nth literals cpos
    val strict = JLit.is_positive literal
    val selected = selected c
  in
    if selected = []
      then Jeha_Order.is_maximal JLit.kbo strict literal literals
      else member (op =) selected cpos
  end

fun is_eligible_full_pos c (tpos, lpos, cpos) =
  let
    val literal = nth (literals c) cpos
    val (s, t, _) = JLit.orient lpos literal
    val s_t_comp = Jeha_KBO.ord (s, t)
    val s_leq_t =
      (SOME LESS = s_t_comp) orelse (SOME EQUAL = s_t_comp)
  in
    is_eligible_cpos c cpos
      andalso not s_leq_t
      andalso is_eligible_tpos s tpos
  end

fun is_position_of_fully_applied_logical_symbol (tpos, lpos, cpos) c =
  subterm_at_full_pos c ([], lpos, cpos)
  |> JTerm.is_position_of_fully_applied_logical_symbol tpos

val is_false = length #> curry (op =) 0

val is_unit = length #> curry (op =) 1

fun is_positive_unit { literals = [lit], ... } = JLit.is_positive lit
  | is_positive_unit _ = false

fun the_unit_lit c =
  if not (is_unit c)
    then error ("the_unit_lit: not a unit" ^ @{make_string} c)
    else the_single (literals c)

fun orient_unit lp = JLit.orient lp o the_unit_lit

end;
