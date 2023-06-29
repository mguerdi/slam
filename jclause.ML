signature JCLAUSE =
sig
  (*
  type cpos = int
  type full_pos = JTerm.tpos * JLit.lpos * cpos
  *)
  include JCLAUSE_POS
  type T
  val literals : T -> JLit.T list
  val id : T -> int
  val maxidx : T -> int
  val maxidx_of2 : T * T -> int
  val map_maxidx : (int -> int) -> T -> T
  val set_origin : Jeha_Log.inference -> T -> T
  val origin : T -> Jeha_Log.inference
  val lit_at : cpos -> T -> JLit.T
  val dummy : JLit.T list -> T
  val refresh_id : unit -> T -> T
  val add_literal : JLit.T -> T -> T
  val combine : T -> T -> T
  val delete_lit_at : cpos -> T -> T
  val filter_out_lits : (JLit.T -> bool) -> T -> T
  val length : T -> int
  val of_literals : JLit.T list * int -> T
  val of_term : term * int -> T
  val term_of : T -> term
  val pretty_clause : Proof.context -> T -> string
  val pretty_clauses : Proof.context -> T list -> string
  val cposs_of : T -> cpos list
  val green_full_poss_of : T -> full_pos list
  val map_at_cpos : cpos -> (JLit.T -> JLit.T) -> T -> T
  val map_at_full_pos : full_pos -> (term -> term) -> T -> T
  val subterm_at_full_pos : T -> full_pos -> term
  val occurs_deeply : term -> T -> bool
  val norm_beta_eta_qeta_env : Envir.env -> T -> T
  val norm_beta_eta_qeta : T -> T
  val incr_indexes : int -> T -> T
  val kbo : T * T -> Jeha_Order.partial_order
  val is_eligible_cpos : T -> cpos -> bool
  val is_eligible_full_pos : T -> full_pos -> bool
  val is_position_of_fully_applied_logical_symbol : full_pos -> T -> bool
end;

structure JClause : JCLAUSE =
struct

open JClause_Pos

type T =
  { literals: JLit.T list
  , id : int
  , maxidx : int
  , origin: Jeha_Log.inference
  }

type cpos = int
type full_pos = JTerm.tpos * JLit.lpos * cpos

val literals = #literals

val id = #id

val maxidx = #maxidx

val maxidx_of2 = Int.max o apply2 maxidx

val empty = { literals = [], id = ~1, maxidx = ~1, origin = Jeha_Log.Invalid }

(* NOTE: invalidates maxidx and origin *)
fun map_literals f { literals, id, maxidx, origin } =
  { literals = f literals, id = id, maxidx = ~1, origin = origin }

fun lit_at cp clause = nth (literals clause) cp

fun dummy literals =
  map_literals (K literals) empty

fun map_id f { literals, id, maxidx, origin } = { literals = literals, id = f id, maxidx = maxidx, origin = origin }

fun refresh_id _ = map_id (K (Clause_Id.new ()))

fun maxidx_of_literal_list ls =
  fold (fn l => fn maxidx => Int.max (JLit.maxidx_of l, maxidx)) ls ~1

fun map_maxidx f { literals, id, maxidx, origin } = { literals = literals, id = id, maxidx = f maxidx, origin = origin }

fun set_origin origin { literals, id, maxidx, ... } = { literals = literals, id = id, maxidx = maxidx, origin = origin }

fun origin { origin, ... } = origin

(* FIXME: use this for testing *)
fun recalculate_maxidx clause =
  map_maxidx ((K o maxidx_of_literal_list o literals) clause) clause

fun add_literal l clause =
  clause
  |> map_literals (cons l)
  |> refresh_id ()
  |> map_maxidx (K (Int.max (maxidx clause, JLit.maxidx_of l)))

fun combine c d =
  map_literals (curry (op @) (literals c)) d
  |> refresh_id ()
  |> map_maxidx (K (maxidx_of2 (c, d)))

fun delete_lit_at cp clause =
  clause
  |> map_literals (nth_drop cp)
  |> refresh_id ()
  |> map_maxidx (K (maxidx clause))

fun filter_out_lits f clause =
  clause
  |> map_literals (filter_out f)
  |> map_maxidx (K (maxidx clause))

val length = List.length o literals

fun of_literals (ls, id) =
  empty |> map_id (K id) |> map_literals (K ls) |> recalculate_maxidx

(* converts boolean terms to lists of literals *)
fun of_term (t, id) =
  if not (fastype_of t = @{typ bool})
    then error "can only turn boolean terms into clauses"
    else
      empty
      |> map_id (K id)
      |> map_literals (K (HOLogic.disjuncts t |> map JLit.of_term))
      |> recalculate_maxidx

fun term_of { literals = [], ... } = @{term False}
  | term_of { literals = (c as (_ :: _)), ... } =
      let
        val (x :: xs) = rev c
      in
        fold (curry HOLogic.mk_disj) (map JLit.term_of xs) (JLit.term_of x)
      end

fun pretty_clause ctxt (c as { id, ... }) =
  @{make_string} id ^ ":" ^ Jeha_Common.pretty_term ctxt (term_of c)

fun pretty_clauses ctxt cs =
  cs
  |> map (fn c =>
      Pretty.block
        [Pretty.str (@{make_string} (#id c) ^ ":")
        , Syntax.pretty_term ctxt (term_of c)
        ])
  |> Pretty.commas
  |> Pretty.block
  |> Pretty.string_of

fun cposs_of c = 0 upto (length c - 1)

fun subterm_at_full_pos { literals, ... } (tp, lp, cp) = JTerm.subterm_at (JLit.term_at_lpos (nth literals cp) lp) tp

fun green_full_poss_of c =
  cposs_of c
  |> maps (fn cp => [JLit.Left, JLit.Right] |> map (fn lp => (subterm_at_full_pos c ([], lp, cp), lp, cp)))
  |> maps (fn (t, lp, cp) => map (fn tp => (tp, lp, cp)) (JTerm.green_tposs_of t))

(* NOTE: invalidates maxidx *)
val map_at_cpos = map_literals oo nth_map

(* NOTE: invalidates maxidx *)
fun map_at_full_pos (tp, lp, cp) f c = map_at_cpos cp (JLit.map_at_lpos lp (JTerm.map_at tp f)) c

fun occurs_deeply (x as (Var _)) { literals, ... } = exists (JLit.occurs_deeply_in x) literals
  | occurs_deeply _ _ = error "only Vars can occur deeply"

fun norm_beta_eta_qeta_env env clause =
  if Envir.maxidx_of env < maxidx clause
    (* this indicates something went wrong *)
    then error "maxidx of env should be greater or equal to maxidx of clause"
    else
      clause
      |> map_literals (map (JLit.map (JTerm.norm_beta_eta_qeta_env env)))
      |> map_maxidx (K (Int.max (Envir.maxidx_of env, maxidx clause)))

fun norm_beta_eta_qeta clause = norm_beta_eta_qeta_env (Envir.empty (maxidx clause)) clause

fun incr_indexes increment clause =
  clause
  |> map_literals (map (JLit.map (Logic.incr_indexes ([], [], increment))))
  |> map_maxidx (K (increment + maxidx clause))

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
    val s_t_comp = Jeha_Order.kbo (s, t)
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
  in
    Jeha_Order.is_maximal JLit.kbo strict literal literals
  end

fun is_eligible_full_pos c (tpos, lpos, cpos) =
  let
    val literal = nth (literals c) cpos
    val (s, t, _) = JLit.orient lpos literal
    val s_t_comp = Jeha_Order.kbo (s, t)
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

end;
