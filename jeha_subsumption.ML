(* multiset subsumption *)

(* Def. c subsumes d iff. \<exists> \<sigma>. c\<sigma> \<subseteq> d as multisets.
i.e. \<exists> \<sigma>. \<forall> l\<sigma> \<in> c\<sigma>. \<exists>! l' \<in> d. l\<sigma> = l'
Algorithm:
Let c = {l\<^sub>1, l\<^sub>2, \<dots>}, d = {l\<^sub>1', l\<^sub>2', \<dots>}, i = 1.
Find l\<^sub>j', \<sigma> s.t. l\<^sub>i\<sigma> = l\<^sub>j', remove l\<^sub>j' from d. Increase i.
Repeat until either subsumed or for l\<^sub>i, no matching l' can be found.
In the latter case backtrack to i <- i-1 and try the next l' for l\<^sub>i. *)

open Jeha_Lang

signature Jeha_Subsumption =
sig
  val literal_matchers : Proof.context -> (literal * literal) -> Envir.env Seq.seq
  (* Extend environment to match second argument against third. *)
  val literal_subsumes : Proof.context -> (literal * literal) -> Envir.env option
  val subsumed_alternatives : Proof.context -> (literal * clause) -> (Envir.env * clause) Seq.seq
  (* Top level clause subsumption. *)
  val subsumes : Proof.context -> (clause * clause) -> bool
end;

structure Jeha_Subsumption =
struct

fun literal_matchers ctxt ((s, t, b), (s', t', b')) =
  if b = b'
    then
      Seq.interleave
        ((Unify.matchers (Context.Proof ctxt) [(s, s'), (t, t')]),
        (Unify.matchers (Context.Proof ctxt) [(s, t'), (t, s')]))
    else
      Seq.empty

fun literal_subsumes ctxt ll' =
  case Seq.pull (literal_matchers ctxt ll') of
    NONE => NONE
    (* throw away the others *)
  | SOME (env, _) => SOME env

(* all ways in which l can subsume a literal of d *)
fun subsumed_alternatives ctxt (l, []) = Seq.empty
  | subsumed_alternatives ctxt (l, l' :: d') = 
      let
        (* recursive call without l', cons l' into the resulting clauses *)
        val skip_l' = (l, d') |> subsumed_alternatives ctxt |> Seq.map (fn (l, d') => (l, l' :: d'))
      in
        case literal_subsumes ctxt (l, l') of
          NONE => skip_l'
          (* FIXME is this lazy or do we need Seq.make? *)
        | SOME env => Seq.cons (env, d') skip_l'
      end

(* read: "c subsumes d" *)
fun subsumes ctxt ([], d) = true
  (* TODO: distinct variables? might not be necessary with Unify.matchers, check! *)
  | subsumes ctxt (l :: ls, d) =
      try_alternatives_with_backtracking ctxt (subsumed_alternatives ctxt (l, d)) ls

and try_alternatives_with_backtracking ctxt alternatives ls =
  case Seq.pull alternatives of
    NONE => false
  | SOME ((env, d_without_l'), alternatives) =>
      let val subsumed =
        let
          (* apply the substitution (only to the subsuming clause) *)
          val ls = (map o map_lit o Envir.subst_term) (Envir.type_env env, Envir.term_env env) ls
        in
          (* move on to next l in ls *)
          subsumes ctxt (ls, d_without_l')
        end
      in
        if subsumed
         then true
         (* backtrack, try the next l' *)
         else try_alternatives_with_backtracking ctxt alternatives ls
      end

end;