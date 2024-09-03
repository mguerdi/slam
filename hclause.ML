signature HCLAUSE =
sig
  type hterm (* = term *)
  type hcterm (* = cterm *)
  type hthm (* = thm *)

  val make_last: JClause.cpos -> hthm -> hthm
  val negate_head: Proof.context -> hthm -> hthm 
  val green_subterm_at_full_pos: hterm -> JClause.full_pos -> hterm
  val term_at_lpos: hterm -> JLit.lpos -> hterm
  val negated_lit_at: JClause.cpos -> hterm -> hterm 
  (* Does not operate on hclauses! *)
  val orient_positive_consequent_lit: JLit.lpos -> thm -> thm
  val abstract_over_green_subterm: JClause.full_pos -> hterm -> int -> hterm
  
  val map_green_subterm_at_full_pos: JClause.full_pos -> (term -> term) -> hterm -> hterm

  val hol_of_clause: Proof.context -> bool -> JClause.T -> hcterm
  (* Don't use this. *)
  val cterm_of: hcterm -> cterm
  val term_of: hcterm -> term
end

structure HClause: HCLAUSE =
struct

(* s = t \<Longrightarrow> u \<noteq> v \<Longrightarrow> ... \<Longrightarrow> False *)
(* The antecedents are called negated (!) literals. *)
(* Properties:
  1. Every antecedent is either an equality or an inequality (no double negations!)
  2. The consequent is "False" *)
type hterm = term
type hcterm = cterm
type hthm = thm

(* Don't use this. *)
fun cterm_of c = c
val term_of = Thm.term_of o cterm_of

(* adapted from metis_reconstruct.ML *)
(*Maps a rule that ends "... ==> P ==> False" to "... ==> ~ P" while avoiding
  to create double negations. *)
fun negate_head ctxt th =
  (* FIXME HClaues.is_hclause ? *)
  if Logic.strip_imp_concl (Thm.prop_of th) = @{prop "False"} then
    th |> fold (rewrite_rule ctxt o single) @{thms not_atomize atomize_not}
  else
    error "negate_head: not a clause"

(* With index 1 turn A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> False into A \<Longrightarrow> C \<Longrightarrow> B \<Longrightarrow> False *)
(*Permute a rule's premises to move the i-th premise to the last position.*)
fun make_last cpos th =
  let
    val n = Thm.nprems_of th
    (* original function was 1-based *)
    val i = cpos + 1
  in
    (* from metis_reconstruct.ML *)
    if i >= 1 andalso i <= n then Thm.permute_prems (i - 1) 1 th
    else raise THM ("make_last", i, [th])
  end

(* \<not>C' \<Longrightarrow> t \<approx> t' *)
(* see JLit.orient *)
(* FIXME: needs to work for disequations? *)
fun orient_positive_consequent_lit JLit.Left C = C
  | orient_positive_consequent_lit JLit.Right C = C COMP_INCR @{thm HOL.sym}

(* Given 1 and (\<not>A \<Longrightarrow> \<not>B \<Longrightarrow> False) returns \<not>B.
Terminology: A and B are the literals of the above clause! *)
fun negated_lit_at cpos hol_clause = 
  let
    val negated_lits = Logic.strip_imp_prems hol_clause
    val () = \<^assert> (@{prop "False"} = Logic.strip_imp_concl hol_clause)
  in
    nth negated_lits cpos
  end

fun map_equality_at_lpos JLit.Left f (Const ("HOL.eq", _) $ x $ y) = HOLogic.mk_eq (f x, y)
  | map_equality_at_lpos JLit.Right f (Const ("HOL.eq", _) $ x $ y) = HOLogic.mk_eq (x, f y)
  | map_equality_at_lpos _ _ t =
      error ("map_equality_at_lpos: not an equality: " ^ @{make_string} t)
  
fun map_at_lpos pos f (@{term "HOL.Not"} $ t) =
      HOLogic.mk_not (map_equality_at_lpos pos f t)
  | map_at_lpos pos f t = map_equality_at_lpos pos f t

fun side_of_equality (Const ("HOL.eq", _) $ x $ _) JLit.Left = x
  | side_of_equality (Const ("HOL.eq", _) $ _ $ y) JLit.Right = y
  | side_of_equality t _ = error ("side_of_equality: not an equality " ^ @{make_string} t)

(* Only strips a single \<not>. *)
fun term_at_lpos (@{term "HOL.Not"} $ t) lp = side_of_equality t lp
  | term_at_lpos t lp = side_of_equality t lp

(* FIXME: This whole endeavour doesn't really make sense because tposs only work on a certain normal
form. Ideas:
  * Always work in o\<lambda>Sups normal form in the reconstruction module.
  * Write on-the-fly subterm retrieval functions that can work on non-normal form terms (favourite).
Orthogonal
  * Change semantic of tpos in HClause.T to treat \<noteq> atomically (i.e. as a single constant symbol
    instead of a \<not> outside an =)
Must-haves:
1. We need to decide on one particular normal form during reconstruction and stick to it.
  Decision: Stick to o\<lambda>Sups normal form. Problem: This is far from what we're doing right now...
2. 
*)
(* This only makes sense for green subterms because of potential differences between the normal form
of o\<lambda>Sup and the one used in proof reconstruction. *)
fun green_subterm_at_full_pos hol_clause (tp, lp, cp) =
  let
    val negated_literal = HOLogic.dest_Trueprop (negated_lit_at cp hol_clause)
    (* Note: Doesn't matter if we do this with the literal or the negated literal. *)
    val side_of_literal = term_at_lpos negated_literal lp
  in
    JTerm.subterm_at side_of_literal tp
  end

fun map_prop_at_cpos cp f hol_clause =
  let
    val negated_lits = Logic.strip_imp_prems hol_clause
    val () = \<^assert> (@{prop "False"} = Logic.strip_imp_concl hol_clause)
  in
    Logic.list_implies (nth_map cp f negated_lits, @{prop "False"})
  end

fun map_green_subterm_at_full_pos (tp, lp, cp) f hol_clause =
  map_prop_at_cpos
    cp
    (HOLogic.mk_Trueprop o map_at_lpos lp (JTerm.map_at tp f) o HOLogic.dest_Trueprop)
    hol_clause

(* Position of a subterm in a hol_clause *)
type hol_full_pos = JTerm.tpos

(* FIXME remove *)
(* Turn a full_pos into a JTerm.tpos that works on hclauses *)
fun hol_clause_pos_of_full_pos ((tpos, lpos, cpos), target_literal_is_positive) = error "remove this"
(*
  (* A\<Longrightarrow>B\<Longrightarrow>\<dots> corresponds to first-orderized \<Longrightarrow>(A,\<Longrightarrow>(B,\<dots>)) therefore: *)
  (* [2,\<dots>,2] (cpos times) to skip over the outer \<Longrightarrow>s *)
  replicate cpos 2
  @ [1 (* left argument of \<Longrightarrow> *)]
  @ [1 (* argument of Trueprop *)]
  (* because a\<noteq>b is \<not>(a=b), and the corresponding *literal* is a=b. *)
  @ (if target_literal_is_positive then [1] else [])
  @ [(if lpos = JLit.Left then 1 else 2)]
  @ tpos
*)

(* The primitve building blocks to which all o\<lambda>Sup inferences can be reduced. *)
(* datatype proof_step =
    (* FIXME: does normalization need to be separate? *)
    Instantiation of { premise: int, substitution: Envir.env }
  | Sup of { left_premise: int, right_premise: int, literal: JLit.lpos * JClause_Pos.cpos, subterm: JClause_Pos.full_pos }
  | ERes of { premise: int, literal: JClause_Pos.cpos }
  | EFact of { premise: int, left_literal: JLit.lpos * JClause_Pos.cpos, right_literal: JLit.lpos * JClause_Pos.cpos }
  (* FIXME: can this be meaningfully viewed as a kind of superposition? *)
  | ArgCong 
  |

fun proof_steps_of_inference *)

(* turn jeha clause [A, B, C] into formula \<not>A \<Longrightarrow> \<not>B \<Longrightarrow> \<not>C \<Longrightarrow> False *)
fun hol_of_clause ctxt close c =
  let
    val negated_literals = 
      JClause.literals c
      |> map (fn (s, t, b) => (s, t, not b))
      |> map JLit.term_of
      |> map HOLogic.mk_Trueprop
    (* FIXME: remove *)
    val vars =
      fold Term.add_vars negated_literals []
      (* reuse variable names for binder names *)
      |> map (fn idxname_typ => (fst (fst idxname_typ), Var idxname_typ))
  in
    if close
      (* FIXME: remove this `if` and the `close` parameter *)
      then
        Logic.close_prop vars negated_literals @{prop "False"}
        (* FIXME: Thm.trim_context_cterm? *)
        |> Thm.cterm_of ctxt
      else
        Logic.list_implies (negated_literals, @{prop "False"})
        |> Thm.cterm_of ctxt
  end

fun abstract_over_green_subterm full_pos hol_clause maxidx =
  let
    val green_subterm = green_subterm_at_full_pos hol_clause full_pos
    (* Note: We can only compute the type because green subterms aren't below lambdas. *)
    val T = fastype_of green_subterm
    val varname = "subterm_at_full_pos"
    val fresh_var = Var ((varname, maxidx + 1), T)
    val term_with_fresh_var_at_tpos = map_green_subterm_at_full_pos full_pos (K fresh_var) hol_clause
    val lambda_inserting_argument_at_tpos =
      Abs (varname, T, abstract_over (fresh_var, term_with_fresh_var_at_tpos))
  in
    lambda_inserting_argument_at_tpos
  end

(* FIXME: delete? *)
(*
(* Given t=t' and (p, L, maxidx) provides L<t>\<^sub>p = L<t'>\<^sub>p. *)
fun congruence_wrt_tpos ctxt (equality : thm) tpos_term_maxidx =
  let
    (* t = t' therefore ?f t = ?f t' *)
    val arg_cong_of_equality = @{thm arg_cong} OF [equality]
    val abstracted_over_tpos =
      abstract_over_tpos tpos_term_maxidx
    val ct = Thm.cterm_of ctxt abstracted_over_tpos
    val cT = Thm.ctyp_of ctxt (fastype_of abstracted_over_tpos)
  in
    Thm.instantiate' [SOME cT] [SOME ct] arg_cong_of_equality
  end
*)

end