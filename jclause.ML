signature JCLAUSE =
sig
  type T
  (* position of literal in a clause *)
  type cpos = int
  type full_pos = JTerm.tpos * JLit.lpos * cpos
  val literals : T -> JLit.T list
  val id : T -> int
  val map_literals : (JLit.T list -> JLit.T list) -> T -> T
  val lit_at : cpos -> T -> JLit.T
  val dummy : JLit.T list -> T
  val refresh_id : T -> T
  val add_literal : JLit.T -> T -> T
  val combine : T -> T -> T
  val delete_lit_at : cpos -> T -> T
  val length : T -> int
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
end;

structure JClause : JCLAUSE =
struct

type T = { literals: JLit.T list, id : int }
type cpos = int
type full_pos = JTerm.tpos * JLit.lpos * cpos

val literals = #literals

val id = #id

fun map_literals f { literals, id } = { literals = f literals, id = id }

fun lit_at cp clause = nth (literals clause) cp

fun dummy literals = { literals = literals, id = ~1 }

fun map_id f { literals, id } = { literals = literals, id = f id }

val refresh_id = map_id (K (Clause_Id.new ()))

fun add_literal l = refresh_id o map_literals (cons l)

fun combine c d =
  map_literals (curry (op @) (literals c)) d |> refresh_id

fun delete_lit_at cp = refresh_id o map_literals (nth_drop cp)

val length = List.length o literals

(* converts boolean terms to lists of literals *)
fun of_term (t, id) =
  if not (fastype_of t = @{typ bool})
    then error "can only turn boolean terms into clauses"
    else { literals = HOLogic.disjuncts t |> map JLit.of_term, id = id }

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

val map_at_cpos = map_literals oo nth_map

fun map_at_full_pos (tp, lp, cp) f c = map_at_cpos cp (JLit.map_at_lpos lp (JTerm.map_at tp f)) c

fun occurs_deeply (x as (Var _)) { literals, ... }= exists (JLit.occurs_deeply_in x) literals
  | occurs_deeply _ _ = error "only Vars can occur deeply"

end;
