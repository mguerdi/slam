signature HCLAUSE =
sig
  type hclause = cterm
  
  val subterm_at_full_pos : term -> JClause.full_pos -> term
  val term_at_lpos : term -> JLit.lpos -> term
  val negated_lit_at : JClause.cpos -> term -> term 
  
  val hol_of_clause: Proof.context -> bool -> JClause.T -> hclause
end

structure HClause: HCLAUSE =
struct

(* s = t \<Longrightarrow> ... \<Longrightarrow> False *)
type hclause = cterm 

(* Given 1 and (\<not>A \<Longrightarrow> \<not>B \<Longrightarrow> False) returns \<not>B.
Terminology: A and B are the literals of the above clause! *)
fun negated_lit_at cpos hol_clause = 
  let
    val negated_lits = Logic.strip_imp_prems hol_clause
    val () = \<^assert> (@{const "False"} = Logic.strip_imp_concl hol_clause)
  in
    nth negated_lits cpos
  end

fun side_of_equality (Const ("HOL.eq", _) $ x $ _) JLit.Left = x
  | side_of_equality (Const ("HOL.eq", _) $ _ $ y) JLit.Right = y
  | side_of_equality t _ = error ("side_of_equality: not an equality" ^ @{make_string} t)

(* Only strips a single \<not>. *)
fun term_at_lpos (@{term "HOL.Not"} $ t) lp = side_of_equality t lp
  | term_at_lpos t lp = side_of_equality t lp

fun subterm_at_full_pos hol_clause (tp, lp, cp) =
  let
    val negated_literal = negated_lit_at cp hol_clause
    (* Note: Doesn't matter if we do this with the literal or the negated literal. *)
    val side_of_literal = term_at_lpos negated_literal lp
  in
    JTerm.subterm_at side_of_literal tp
  end

(* Position of a subterm in a hol_clause *)
type hol_full_pos = JTerm.tpos

fun hol_clause_pos_of_full_pos (tpos, lpos, cpos) =
  cpos :: 1 (* argument of Trueprop *) :: (if lpos = JLit.Left then 0 else 1) :: tpos

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

end