(* Abstract simplification algorithm, supporting simplifications which return multiple clauses. *)

signature JEHA_SIMPLIFY =
sig
  type unit_index = term -> JClause.T list
  type simp_fun = unit_index -> JClause.T -> JClause.T list
  val first_successful_rewrite : unit_index -> JClause.T -> simp_fun list -> JClause.T list
  val simplify_first :
        Proof.context -> simp_fun list -> unit_index -> JClause.T list -> JClause.T list -> int
          -> JClause.T list * JClause.T list
  val simplify_all : Proof.context -> simp_fun list -> unit_index -> int -> JClause.T
        -> JClause.T list * JClause.T list
  (* Applies simp_funs in order until no more apply or a countdown has been reached.
  returns
     [] -> redundant
     SOME [c] -> simplified or original clause (if no simplification possible) 
     SOME (c::cs) -> one or more simplified clauses *)
  val simplify : bool -> Proof.context -> simp_fun list -> unit_index -> JClause.T
        -> JClause.T list * JClause.T list
end;

structure Jeha_Simplify : JEHA_SIMPLIFY =
struct

type unit_index = term -> JClause.T list

type simp_fun = unit_index -> JClause.T -> JClause.T list

(* If there is more than one simplification we only keep simplifying the first one. *) 

(* FIXME: First clause turns out to be redundant, need to restart simplification with the second
one, repeat until one can't be simplified further or all are redundant.
Alternative:
Put everything back into passive set, start next iteration.
Requires separating out redundancy check into separate call in given clause loop. *)

(* Try simp_funs in order, return when one succeeds. *)
fun first_successful_rewrite _ _ [] = [] (* no rewrite possible *)
  | first_successful_rewrite index clause (simp_fun::simp_funs) =
      case simp_fun index clause of
        [] => first_successful_rewrite index clause simp_funs
      | simplifications => simplifications

(* for full simplification: *)

(* simplify a clause once *)
fun once_simplify index simp_funs clause (once_simplified, fully_simplified, archive) =
  case first_successful_rewrite index clause simp_funs of
    [] => (once_simplified, clause::fully_simplified, archive)
  | simplifications =>
      (simplifications @ once_simplified, fully_simplified, clause::archive)

(* Fully simplify clauses, accumulating fully simplified clauses and archive.
Think: repeated flat_map of first_successful_rewrite over clauses. *)
fun full_simplify_all _ _ _ 0 (partially_simplified, fully_simplified, archive) =
      let val _ = writeln "simplify_first: full_rewrite countdown reached" in
        (partially_simplified @ fully_simplified, archive)
      end
  | full_simplify_all _ _ _ _ ([], fully_simplified, archive) =
      (fully_simplified, archive) (* all clauses fully simplified *)
  | full_simplify_all ctxt simp_funs index countdown (partially_simplified, fully_simplified, archive) =
      (* Fresh accumulator for results of one-step simplification of partially_simplified. *) 
      ([], fully_simplified, archive)
      |> fold (once_simplify index simp_funs) partially_simplified 
      |> full_simplify_all ctxt simp_funs index (countdown - 1)

fun simplify_all ctxt simp_funs index countdown clause =
  full_simplify_all ctxt simp_funs index countdown ([clause], [], [])

(* Fully simplify the first among a list of clauses. *)
fun simplify_first _ _ _ [] _ _ = error "simplify_first: no clause to simplify!"
  | simplify_first _ _ _ simplifications archive 0 =
      let val _ = writeln "simplify_first: full_rewrite countdown reached" in
        (simplifications, archive)
      end
  | simplify_first
      ctxt
      simp_funs
      index
      (* other_simplifications and archive are accumulators for tail recursion *)
      (clause::other_simplifications)
      archive
      countdown
      =
      case first_successful_rewrite index clause simp_funs of
        [] =>
          let val _ = Jeha_Common.trace_msg ctxt (fn () =>
            "done rewriting " ^ JClause.pretty_clause ctxt clause ^ ".")
          in
            (clause::other_simplifications, archive) (* clause can't be simplified further *)
          end
      | simplifications => 
          simplify_first
            ctxt
            simp_funs
            index
            (* we'll keep simplifying the first element of this list *)
            (simplifications @ other_simplifications)
            (* add unsimplified (now redundant) clause to archive for proof reconstruction *)
            (clause :: archive)
            (countdown - 1)

(* Fully simplify a list of clauses *)
(* FIXME: countdown is wrong, depends on when extra clauses were created
Solutions:
1. track simplification depth with each clause
2.
  unsimplified : (int * JClause.T list) list
  simplify_all
    ctxt
    simp_funs
    index
    ((countdown, unsimplified)::other_unsimplified)
    archive
    simplified
  =
    val (simplified_clause::unsimplified, archive) =
      simplify_first ctxt simp_funs index unsimplified archive countdown
    in
      simplify_all ctxt simp_funs index ((countdown - 1)::other_unsimplified)
3.
type simp_clause = int * JClause.T

*)
(* fun simplify_all _ _ _ [] archive simplified _ = (simplified, archive)
  | simplify_all ctxt simp_funs index unsimplified archive simplified countdown =
  let
    val (simplified_clause::unsimplified, archive) =
      simplify_first ctxt simp_funs index unsimplified archive countdown
  in
    simplify_all ctxt simp_funs index unsimplified archive (simplified_clause::simplified) countdown
  end
*)

fun simplify only_first ctxt simp_funs index clause =
  let val countdown = 10 in
  if only_first
    then simplify_first ctxt simp_funs index [clause] [] countdown
    else simplify_all ctxt simp_funs index countdown clause
  end

(* Index of active units?
Traverse term, looking in index for active units
* RP, RN: simple, though breadth first search probably ideal?
    (reasoning: simplifying )
* bit counterintuitive: PS (find single disagreement, find matching unit)
* NS (find generalization of literal among units)
* ES: see PS *)

end;
