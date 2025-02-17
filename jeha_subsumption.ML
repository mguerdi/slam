(* multiset subsumption *)

(* Def. c subsumes d iff. \<exists> \<sigma>. c\<sigma> \<subseteq> d as multisets.
i.e. \<exists> \<sigma>. \<forall> l\<sigma> \<in> c\<sigma>. \<exists>! l' \<in> d. l\<sigma> = l'
Algorithm:
Let c = {l\<^sub>1, l\<^sub>2, \<dots>}, d = {l\<^sub>1', l\<^sub>2', \<dots>}, i = 1.
Find l\<^sub>j', \<sigma> s.t. l\<^sub>i\<sigma> = l\<^sub>j', remove l\<^sub>j' from d. Increase i.
Repeat until either subsumed or for l\<^sub>i, no matching l' can be found.
In the latter case backtrack to i <- i-1 and try the next l' for l\<^sub>i. *)

signature JEHA_SUBSUMPTION =
sig
  (* Extend environment to match second argument against third. *)
  val literal_subsumes : Context.generic -> int -> (JLit.T * JLit.T) -> Envir.env option
  val subsumed_alternatives :
    Context.generic -> int -> (JLit.T * JLit.T list) -> (Envir.env * JLit.T list) Seq.seq
  (* Top level clause subsumption. *)
  val subsumes : Context.generic -> (JClause.T * JClause.T) -> bool
end;

structure Jeha_Subsumption : JEHA_SUBSUMPTION =
struct

fun literal_subsumes ctxt maxidx ll' =
  (* (writeln ("literals subumes:" ^ JLit.pretty_lit (Context.the_proof ctxt) (#1 ll') ^ " can match? " ^ JLit.pretty_lit (Context.the_proof ctxt) (#2 ll')); *)
  case Seq.pull (Jeha_Unify.literal_matchers ctxt maxidx ll') of
    NONE => (* (writeln "=> no"; *) NONE (* ) *)
    (* throw away the others *)
  | SOME ((_, env), _) => (* (writeln "=> yes"; *) SOME env (* ) *)
  (* ) *)

(* all ways in which l can subsume a literal of d *)
(* FIXME: lazify with make / pull if it isn't yet. *)
(* FIXME: tail recursive version? *)
fun subsumed_alternatives ctxt maxidx (l, []) = Seq.empty
  | subsumed_alternatives ctxt maxidx (l, l' :: d') = 
      let
        (* recursive call without l', keep l' around for later *)
        fun skip_l' maxidx' =
          (l, d')
          |> subsumed_alternatives ctxt maxidx'
          (* d'' is d' but with one literal removed because it was subsumed by l *)
          |> Seq.map (fn (env, d'') => (env, l' :: d''))
      in
        case literal_subsumes ctxt maxidx (l, l') of
          (* l can't subsume l' *)
          NONE => skip_l' maxidx
          (* l can subsume l', but still try the alternatives afterwards *)
        | SOME env => Seq.cons (env, d') (skip_l' (Envir.maxidx_of env))
      end

(* read: "c subsumes d" *)
fun impl_subsumes ctxt _ ([], d) = true
  | impl_subsumes ctxt maxidx (l :: ls, d) =
      try_alternatives_with_backtracking ctxt (subsumed_alternatives ctxt maxidx (l, d)) ls

and try_alternatives_with_backtracking ctxt alternatives ls =
  case Seq.pull alternatives of
    NONE => false
  | SOME ((env, d_without_l'), alternatives) =>
      let val subsumed =
        let
          (* apply the substitution (only to the subsuming clause) *)
          val ls = (map o JLit.map o JTerm.norm_beta_eta_qeta_env) env ls
        in
          (* move on to next l in ls *)
          (* FIXME: do we need to check that env is consistent with later envs, i.e. they combine to
          form a valid substitution? No: the variables mapped by env are do not occur anymore after
          it has been applied (what about the ones not mapped by env? Note: env is total w.r.t. l,
          because its variables are distinct from those of l'. *)
          impl_subsumes ctxt (Envir.maxidx_of env) (ls, d_without_l')
        end
      in
        if subsumed
         then true
         (* backtrack, try the next l' *)
         else try_alternatives_with_backtracking ctxt alternatives ls
      end

val subsumption_ord = prod_ord int_ord int_ord

fun subsumption_sort_key (l, r, sign) =
  (if sign then 1 else ~1, size_of_term l + size_of_term r)

fun subsumption_sort lits =
  let
    val keys = map subsumption_sort_key lits
    val idxs = 0 upto (length lits - 1)
    val idxs_sorted = sort (subsumption_ord o apply2 (nth keys)) idxs
    val lits_sorted = map (nth lits) idxs_sorted
  in
    lits_sorted 
  end

fun subsumes ctxt (c, d) =
  let
    (* make vars of c (the pattern) distinct from those of d *)
    val c = JClause.incr_indexes (JClause.maxidx d + 1) c
    (* to ensure generate variables are fresh w.r.t. both clauses *)
    val maxidx = JClause.maxidx_of2 (c, d)
    (* val _ = writeln ("check if " ^ JClause.pretty_clause (Context.the_proof ctxt) c ^ " subsumes " ^ JClause.pretty_clause (Context.the_proof ctxt) d) *)
    val (c_lits, d_lits) = apply2 JClause.literals (c, d)
    val (c_lits_sorted, d_lits_sorted) = apply2 subsumption_sort (c_lits, d_lits)
  in
    impl_subsumes ctxt maxidx (c_lits_sorted, d_lits_sorted)
  end

end;