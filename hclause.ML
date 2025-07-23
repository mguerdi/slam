signature HCLAUSE =
sig
  (* An hclause is of the form
    sk1 = (\<lambda>\<dots> SOME\<dots>) \<Longrightarrow> \<dots> \<Longrightarrow> s = t \<Longrightarrow> u \<noteq> v \<Longrightarrow> \<dots> \<Longrightarrow> False
  where the premises of the form sk1 \<noteq> (\<lambda>\<dots> SOME\<dots>) are kept track of and not considered to be part
  of the clause (in the sense of the calculus). They are necessary to ensure the correct
  interpretation of variables which represent skolem constants. As the last step of proof
  reconstruction the clause False, which is in the form of
    sk1 = (\<lambda>\<dots> SOME\<dots>) \<Longrightarrow> \<dots> \<Longrightarrow> skN = \<dots> \<Longrightarrow> False
  is turned into
    False
  by first generalizing the free variables sK1, \<dots>, skN to obtain 
    ?sk1 = (\<lambda>\<dots> SOME\<dots>) \<Longrightarrow> \<dots> \<Longrightarrow> ?skN = \<dots> \<Longrightarrow> False
  and applying the trivial substitution solving the premises.

  This module contains the necessary utilities to carry along the skolem premises during proof
  reconstruction, making sure they are always to the left of the actual clause. *)
  
  (* The \<dots>_raw functions do not take into account the skolem premises and consider them to be part
  of the clause. *)

  type hterm
  type hcterm
  type hthm

  val hterm_of : hthm -> hterm
  val thm_of : hthm -> thm
  val map_hthm : (thm -> thm) -> hthm -> hthm
  val traverse_hthm : (thm -> thm list) -> hthm -> hthm list
  
  val cprop_without_skolem_prems : hthm -> cterm
  
  val of_lemma : thm -> hthm
  
  val maxidx_of : hthm -> int
  val nprems_of : hthm -> int

  val make_last: JClause.cpos -> hthm -> hthm
  val move_last_to: JClause.cpos -> hthm -> hthm
  val move_from_to: JClause.cpos -> JClause.cpos -> hthm -> hthm
  val negate_head: Proof.context -> hthm -> { th: thm, skolems: (term * term) list }
  val green_subterm_at_full_pos: hterm -> JClause.full_pos -> term
  val term_at_lpos: term -> JLit.lpos -> term
  val negated_lit_trueprop_cterm_at: JClause.cpos -> hthm -> cterm
  val negated_lit_trueprop_term_at: JClause.cpos -> hterm -> term
  val dest_lit_cterm_at: JClause.cpos -> hthm -> cterm * cterm * bool (* compare JLit.T *)
  val dest_lit_at: JClause.cpos -> hthm -> term * term * bool
  val orient_lit_at: (JLit.lpos * JClause.cpos) -> hthm -> hthm
  (* Does not operate on hclauses! *)
  val orient_positive_consequent_lit: JLit.lpos -> thm -> thm
  val abstract_over_green_subterm: JClause.full_pos -> hterm -> int -> term

  val map_green_subterm_at_full_pos_raw: JClause.full_pos -> (term -> term) -> term -> term
  val map_green_subterm_at_full_pos: JClause.full_pos -> (term -> term) -> hterm -> hterm

  val hol_of_clause: Proof.context -> bool -> JClause.T -> cterm

  val merge_duplicated_lit_last: hthm -> hthm 
  
  (* 1-based *)
  val comp_no_flatten_no_incr: hthm * int -> int -> hthm -> hthm
  val comp_no_flatten: hthm * int -> int -> hthm -> hthm
  val compose : thm * int * hthm -> hthm

  (* protects skolems *)
  val incr_indexes : int -> hthm -> hthm
  
  val congruence_wrt_subterm_position : Proof.context -> term * term -> hthm -> JClause.full_pos -> hthm
end

structure HClause: HCLAUSE =
struct

val dest_Trueprop = Thm.dest_arg

(* s = t \<Longrightarrow> u \<noteq> v \<Longrightarrow> ... \<Longrightarrow> False *)
(* The antecedents are called negated (!) literals. *)
(* Properties:
  1. Every antecedent is either an equality or an inequality (no double negations!)
  2. The consequent is "False" *)
(* FIXME: Use constructors to make these opaque? *)
(* FIXME: maybe `skolems: int` suffices *)
type hterm = { t: term, skolems: (term * term) list }
type hcterm = { ct: cterm, skolems: (term * term) list }
(* FIXME: generalize to allow arbitrary lists of implications as thms (as long as the conclusion is
not a skolem premise?) and then specialize to "hthm" which allows only False as conclusion.
(Something involving "clause" would be a better name) *)
type hthm = { th: thm, skolems: (term * term) list }

fun thm_of { th, ... } = th
fun map_hthm f { th = th, skolems = skolems } = { th = f th, skolems = skolems }
fun map_hterm f { t = t, skolems = skolems } = { t = f t, skolems = skolems }
fun hterm_of { th = th, skolems = skolems } = { t = Thm.prop_of th, skolems = skolems }
fun term_of { t, ... } = t

(* name borrowed from Haskell Traversable *)
fun traverse_hthm (f : thm -> thm list) { th, skolems } : hthm list =
  map (fn th' => { th = th', skolems = skolems }) (f th)

fun of_lemma th = { th = th, skolems = [] }

fun maxidx_of { th, ... } = Thm.maxidx_of th

fun cprop_without_skolem_prems { th, skolems } =
  funpow (length skolems) (snd o Thm.dest_implies) (Thm.cprop_of th)

(* adapted from metis_reconstruct.ML *)
(*Maps a rule that ends "... ==> P ==> False" to "... ==> ~ P" while avoiding
  to create double negations. *)
fun negate_head ctxt { th = th, skolems = skolems } =
  (* FIXME HClause.is_hclause ? *)
  if Logic.strip_imp_concl (Thm.prop_of th) = @{prop "False"} then
    { th = th |> fold (rewrite_rule ctxt o single) @{thms not_atomize atomize_not}
    , skolems = skolems
    }
  else
    error "negate_head: not a clause"

(* With index 1 turn A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> False into A \<Longrightarrow> C \<Longrightarrow> B \<Longrightarrow> False *)
(*Permute a rule's premises to move the i-th premise to the last position.*)
fun make_last cpos { th = th, skolems = skolems } =
  let
    (* original function was 1-based *)
    val i = cpos + 1 + length skolems
  in
    { th = Jeha_Proof_Util.make_prem_last i th, skolems = skolems }
  end

(* Like make_last but rotate right by one instead of left. *)
fun move_last_to cpos { th = th, skolems = skolems } =
  let
    val i = cpos + 1 + length skolems
  in
    { th = Jeha_Proof_Util.move_last_prem_to i th, skolems = skolems }
  end

fun move_from_to (from: JClause.cpos) (to: JClause.cpos) =
  map_hthm (Jeha_Proof_Util.move_prem_from_to (from + 1) (to + 1))

(* \<not>C' \<Longrightarrow> t \<approx> t' *)
(* see JLit.orient *)
(* FIXME: needs to work for disequations? *)
fun orient_positive_consequent_lit JLit.Left C = C
  | orient_positive_consequent_lit JLit.Right C =
      Drule.comp_no_flatten (C, Thm.nprems_of C) 1 (Drule.incr_indexes C @{thm HOL.sym})

fun nprems_of { th, skolems } = Thm.nprems_of th - length skolems

(* Given 1 and (\<not>A \<Longrightarrow> \<not>B \<Longrightarrow> False) returns \<not>B.
Terminology: A and B are the literals of the above clause! *)
fun negated_lit_trueprop_cterm_at_raw cpos th = 
  let
    val negated_lits = Drule.strip_imp_prems (Thm.cprop_of th)
    val () = \<^assert> (@{cprop "False"} aconvc Drule.strip_imp_concl (Thm.cprop_of th))
  in
    nth negated_lits cpos
  end

fun negated_lit_trueprop_cterm_at cpos { th = th, skolems = skolems } = 
  negated_lit_trueprop_cterm_at_raw (cpos + length skolems) th 

fun dest_lit_cterm_at cpos hol_clause =
  let
    val negated_lit = Thm.dest_arg (negated_lit_trueprop_cterm_at cpos hol_clause)
    val negated_lit_is_positive = not (can HOLogic.dest_not (Thm.term_of negated_lit))
    val (left, right) =
      negated_lit
      |> (if negated_lit_is_positive then I else Thm.dest_arg)
      |> Drule.strip_comb 
      |> (fn (_, [left, right]) => (left, right))
  in
    (left, right, not negated_lit_is_positive)
  end

fun dest_lit_at cpos hol_clause =
  let val (s, t, b) = dest_lit_cterm_at cpos hol_clause in (Thm.term_of s, Thm.term_of t, b) end

fun negated_lit_trueprop_term_at_raw cpos (hol_clause: term) =
  let
    val negated_lits = Logic.strip_imp_prems hol_clause
    val () = \<^assert> (@{prop "False"} aconv Logic.strip_imp_concl (hol_clause))
  in
    nth negated_lits cpos
  end
  

(* Given 1 and (\<not>A \<Longrightarrow> \<not>B \<Longrightarrow> False) returns \<not>B.
Terminology: A and B are the literals of the above clause! *)
fun negated_lit_trueprop_term_at cpos (hol_clause as { skolems = skolems, ... }) =
  negated_lit_trueprop_term_at_raw (cpos + length skolems) (term_of hol_clause)

(* compare JLit.orient *)
fun orient_lit_at (JLit.Left, _) hclause = hclause
  | orient_lit_at (JLit.Right, cpos) (hclause as { th = th, skolems = skolems }) =
      let
        val negated_lit =
          HOLogic.dest_Trueprop (negated_lit_trueprop_term_at cpos (hterm_of hclause))
        val is_positive = can HOLogic.dest_not negated_lit
        val lemma = if is_positive then @{thm "HOL.not_sym"} else @{thm "HOL.sym"}
      in
        { th = lemma RSN (cpos + 1 + length skolems, th), skolems = skolems }
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
fun green_subterm_at_full_pos_raw (hol_clause: term) (tp, lp, cp) =
  let
    val negated_literal =
      HOLogic.dest_Trueprop (negated_lit_trueprop_term_at_raw cp hol_clause)
    (* Note: Doesn't matter if we do this with the literal or the negated literal. *)
    val side_of_literal = term_at_lpos negated_literal lp
  in
    JTerm.subterm_at side_of_literal tp
  end

fun green_subterm_at_full_pos { t = hol_clause, skolems = skolems } (tp, lp, cp) =
  green_subterm_at_full_pos_raw hol_clause (tp, lp, cp + length skolems)

fun map_prem_at i f (hol_clause: term) =
  let
    val prems = Logic.strip_imp_prems hol_clause
    val () = \<^assert> (@{prop "False"} = Logic.strip_imp_concl hol_clause)
  in
    Logic.list_implies (nth_map (i - 1) f prems, @{prop "False"})
  end

fun map_green_subterm_at_full_pos_raw (tp, lp, cp) f (hol_clause: term) =
  map_prem_at
    (cp + 1)
    (HOLogic.mk_Trueprop o map_at_lpos lp (JTerm.map_at tp f) o HOLogic.dest_Trueprop)
    hol_clause

fun map_green_subterm_at_full_pos (tp, lp, cp) f (hol_clause as { skolems = skolems, ... }) =
  map_hterm
    (map_green_subterm_at_full_pos_raw (tp, lp, cp + length skolems) f)
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

(* Turn jeha clause [A, B, C] into formula \<not>A \<Longrightarrow> \<not>B \<Longrightarrow> \<not>C \<Longrightarrow> False, avoiding double negations. *)
fun hol_of_clause ctxt close c =
  let
    val negated_literals = 
      JClause.literals c
      |> map (fn (s, t, b) => (s, t, not b)) (* avoid double negations *)
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

(* FIXME: Would be nice to move this to Jeha_Proof_Util but there it should use a 1-based notion of
green position which we don't have. *)
fun abstract_over_green_subterm_raw full_pos (hol_clause: term) maxidx =
  let
    val green_subterm: term = green_subterm_at_full_pos_raw hol_clause full_pos
    (* Note: We can only compute the type because green subterms aren't below lambdas. *)
    val T = fastype_of green_subterm
    val varname = "subterm_at_full_pos"
    val fresh_var = Var ((varname, maxidx + 1), T)
    val term_with_fresh_var_at_tpos: term =
      map_green_subterm_at_full_pos_raw full_pos (K fresh_var) hol_clause
    val lambda_inserting_argument_at_tpos =
      Abs (varname, T, abstract_over (fresh_var, term_with_fresh_var_at_tpos))
  in
    lambda_inserting_argument_at_tpos
  end

fun abstract_over_green_subterm full_pos { t = hol_clause, skolems = skolems } maxidx =
  let
    val (tp, lp, cp) = full_pos
    val full_pos = (tp, lp, cp + length skolems)
  in
    abstract_over_green_subterm_raw full_pos hol_clause maxidx
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

(* C = \<not>C' \<Longrightarrow> A \<Longrightarrow> A \<Longrightarrow> False *)
(* ============================= *)
(*      \<not>C' \<Longrightarrow> A \<Longrightarrow> False      *)
fun merge_duplicated_lit_last { th = C, skolems = skolems } =
  let
    val length_of_C'_and_skolems = Thm.nprems_of C - 2
    val () = \<^assert> (length_of_C'_and_skolems - length skolems >= 0)
    val A = Thm.dest_arg (Thm.cprem_of C (Thm.nprems_of C))
    val A' = Thm.dest_arg (Thm.cprem_of C (Thm.nprems_of C - 1))
    val () = \<^assert> (A aconvc A')
    val lemma = \<^instantiate>\<open>P = A in lemma \<open>(P \<Longrightarrow> P \<Longrightarrow> False) \<Longrightarrow> P \<Longrightarrow> False\<close> by auto\<close>
                                            (* ^^^^^^^^^^^^^^ *)
                                            (*      |         *)
    val D = Drule.comp_no_flatten (C, length_of_C'_and_skolems) 1 lemma
      (* See also: comp_hhf_tac (Pure/Isar/proof_context.ML) *)
      (* Thm.bicompose
        (SOME ctxt)
        {flatten = false,  match = false, incremented = false}
        (false, C, 1)
        1
        lemma
      |> Seq.hd *)
  in
    { th = D, skolems = skolems }
  end

fun skolem_constant_variables { th, skolems } =
  map (fn cpos => negated_lit_trueprop_cterm_at_raw cpos th) (0 upto (length skolems - 1))

(* Increments all variables *)
fun incr_indexes shift { th, skolems } =
  { th = Thm.incr_indexes shift th
  , skolems = map (apply2 (Logic.incr_indexes ([], shift))) skolems
  }

fun comp_no_flatten
  ({ th = th1, skolems = skolems1 }, n)
  i
  { th = th2, skolems = skolems2 }
=
  let
    val th_with_skolems2_in_middle =
      Drule.comp_no_flatten
        (th1, length skolems1 + n)
        (length skolems2 + i)
        th2
    val th_with_skolems2_right_of_skolems1 =
      Jeha_Proof_Util.move_prems_left
        (Thm.nprems_of th1 + 1)
        (length skolems2)
        (Thm.nprems_of th1 - length skolems1)
        th_with_skolems2_in_middle
  in
    { th = th_with_skolems2_right_of_skolems1, skolems = skolems1 @ skolems2 }
  end

(* 1-based *)
fun comp_no_flatten_no_incr
  ({ th = th1, skolems = skolems1 }, n)
  i
  { th = th2, skolems = skolems2 }
=
  let
    (* th1 = sk1 \<Longrightarrow> A \<Longrightarrow> B *)
    (*                     ^ n = 1 (number of protected prems) *)
    (* th2 = sk2 \<Longrightarrow> D \<Longrightarrow> B \<Longrightarrow> F *)
    (*                     ^ i = 2 (target prem) *)
    val th_with_skolems1_in_middle =
      Jeha_Proof_Util.comp_no_flatten_no_incr
        (th1, length skolems1 + n)
        (length skolems2 + i)
        th2
    (* th_with_skolems1_in_middle = sk2 \<Longrightarrow> D \<Longrightarrow> sk1 \<Longrightarrow> A \<Longrightarrow> F *)
    val th_with_skolems1_left_of_skolems2 =
      Jeha_Proof_Util.move_prems_left
        (length skolems2 + i)     (* from: sk1 is now where target prem was *)
        (length skolems1)         (* how many *)
        (length skolems2 + i - 1) (* how far: move over sk2 \<Longrightarrow> D *)
        th_with_skolems1_in_middle
    (* th_with_skolems1_left_of_skolems2 = sk1 \<Longrightarrow> sk2 \<Longrightarrow> D \<Longrightarrow> A \<Longrightarrow> F *)
  in
    { th = th_with_skolems1_left_of_skolems2, skolems = skolems1 @ skolems2 }
  end

(* Drule.compose, first argument is a thm, i.e. something that does not contain skolem premises,
e.g. some helper lemma. *)
fun compose (th_left, i, { th, skolems }) =
  { th = Drule.compose (th_left, i + length skolems, th), skolems = skolems }

(* From (t, t'), \<not>C\<langle>t\<rangle>\<^sub>p \<Longrightarrow> False and p build
  t = t' \<Longrightarrow> \<not>C\<langle>t'\<rangle>\<^sub>p \<Longrightarrow> False
with skolem premises of \<not>C\<langle>t'\<rangle>\<^sub>p to the left of t = t'. *)
fun congruence_wrt_subterm_position ctxt eq (c as { skolems, ... }) subterm_position =
  let
    val (ct, ct') = apply2 (Thm.cterm_of ctxt) eq
    val cT = Thm.ctyp_of_cterm ct
    (* x \<mapsto> (\<not>C\<langle>x\<rangle>\<^sub>p \<Longrightarrow> False) *)
    val C_abs =
      abstract_over_green_subterm
        subterm_position
        (hterm_of c)
        (* We could do without this if we could assume that all schematic variables are fixed
        because this variable is short lived anyways. *)
        (maxidx_of c)
      |> Thm.cterm_of ctxt
    val C_congruence_wrt_subterm_position =
      (* Without PROP the parser refuses to read f as having return type prop (instead of bool). *)
      \<^instantiate>\<open>x=ct and y=ct' and f=C_abs and 'a=cT in
        lemma \<open>(x :: 'a) = y \<Longrightarrow> PROP f x \<Longrightarrow> PROP f y\<close> by auto\<close>
      (* Get's rid of the PROP f x premise *)
      |> (fn th => Drule.compose (thm_of c, 2, th)) 
      (* Move the skolem premises that are part of PROP f y above to the very left. *)
      |> Jeha_Proof_Util.move_prems_left 2 (length skolems) 1
  in
    { th = C_congruence_wrt_subterm_position, skolems = skolems } 
  end

end