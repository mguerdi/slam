theory jeha_lemma

imports jeha_base (* HOL.Sledgehammer *) HOL.Hilbert_Choice

begin

declare [[show_types]]

ML \<open>
  (* Goal: Only instantiate the term variables. Instantiate type variables as required by the term
  instantiation.
  1. Collect all term variables
  2. Compare to the given term instantiations and deduce necessary type instantiations
  3. Perform type instantiations
  4. Perform term instantiations
  *)
  (* Difficult because we need to have the thm's variables in the same order as in the implementation
  of Thm.instantiate'
  fun deduce_type_instantiations ts thm =
    let
      val vars = fold Term.add_vars [] ts
    in
      error "unimplemented"
    end *)
\<close>

(* from SMT.thy *)
lemma verit_sko_forall: \<open>(\<forall>x. P x) \<longleftrightarrow> P (SOME x. \<not>P x)\<close>
  by (insert someI[of \<open>\<lambda>x. \<not>P x\<close>], auto)

ML \<open>
  (* Use Thm.instantiate and assume that P is Var (("P", 0), _) *)
  (* fun forall_rw_lemma ctxt predicate = fastype_instantiate' ctxt T *)
      (* we can't say [NONE] and have it figure out the type by itself *)
      (* Thm.instantiate' [SOME T] [SOME P] @{thm verit_sko_forall} *)
  

  (* Alternative: Old Version 
  fun forall_rw_lemma ctxt predicate =
    let
      val T = fastype_of predicate |> domain_type |> Thm.ctyp_of ctxt
      val P = Thm.cterm_of ctxt predicate
    in
      (* FIXME: is there a way of not instantiating 'a explicitly? See verit_sko_forall proof? *)
      \<^instantiate>\<open>
        P and 'a=T in lemma (open) \<open>(\<forall>x. P x) \<longleftrightarrow> P (SOME x. \<not>P x)\<close>
        by
        (* (auto intro ! : someI[of \<open>\<lambda>x. \<not>P x\<close>]) *)
        (* (auto simp add : someI[of \<open>\<lambda>x. \<not>P x\<close>]) *)
        (* (force simp add : someI some_eq_imp) *)
        (insert someI[of \<open>\<lambda>x. \<not>P x\<close>]) auto
        \<close>
    end
  *)
  
  (*
  val p = @{term "\<lambda> x :: bool . x"}
  
  val frwp = forall_rw_lemma @{context} p
  *)
\<close>

lemma LEM: \<open>P \<or> \<not>P\<close>
  by auto

ML \<open>
  fun lem_lemma ctxt t =
    let
      val cT = Thm.ctyp_of ctxt (fastype_of t)
      val ct = Thm.cterm_of ctxt t
    in
      Thm.instantiate' [SOME cT] [SOME ct] @{thm LEM}
    end
\<close>

(* This is the contrapositive of what Isabelle calls "fun_cong" *)
lemma arg_cong_contrapositive: \<open>s x \<noteq> s' x \<Longrightarrow> s \<noteq> s'\<close>
  by auto

(* FIXME: delete 
ML \<open>
  fun arg_cong_lemma ctxt s s' x =
    let
      val cs = Thm.cterm_of ctxt s
      val cs' = Thm.cterm_of ctxt s'
      val cx = Thm.cterm_of ctxt x
      val cT = Thm.ctyp_of ctxt (fastype_of s)
      val cT' = Thm.ctyp_of ctxt (fastype_of s')
      val cTx = Thm.ctyp_of ctxt (fastype_of x)
    in
      Thm.instantiate' [SOME cT, SOME cTx, SOME cT'] [SOME cs, SOME cx, SOME cs'] @{thm arg_cong_contrapositive}
    end
\<close> *)

lemma sup_full_inference:
  "   (\<not>D \<Longrightarrow> t \<noteq> t' \<Longrightarrow> False)
  \<Longrightarrow> (\<not>C' \<Longrightarrow> \<not>(L t) \<Longrightarrow> False)
  \<Longrightarrow> \<not>D \<Longrightarrow> \<not>C' \<Longrightarrow> \<not>(L t') \<Longrightarrow> False"
  by auto

ML \<open>
\<close>

lemma forall_hoist_just_to_be_safe:
  "((\<forall>x. P x) = True \<Longrightarrow> (\<forall>x. P x) = False \<Longrightarrow> False) \<equiv> (\<And>x.((\<forall>x. P x) = True \<Longrightarrow> P x = False \<Longrightarrow> False))"
  by auto

lemma not_atomize: "(\<not> A \<Longrightarrow> False) \<equiv> Trueprop A"
by (cut_tac atomize_not [of "\<not> A"]) simp

(* BoolRw *)

ML \<open>
signature JEHA_LEMMA = sig
  (* FIXME: the result of these should really be HClause.hthm *)
  val hclause_of_uninstantiated_bool_rw_rule: Proof.context -> term * term -> thm
  val forall_exists_rw_lemma: Proof.context -> cterm -> bool -> thm
end

structure Jeha_Lemma: JEHA_LEMMA = struct
(* see Jeha.bool_rw_non_var_rules *)
fun hclause_of_uninstantiated_bool_rw_rule ctxt (lhs, rhs) =
  let
    val (lhs, rhs) = apply2 (Thm.cterm_of ctxt) (lhs, rhs)
    val T = Thm.ctyp_of_cterm lhs
    val cprop = \<^instantiate>\<open>lhs and rhs and 'a=T in cprop \<open>(lhs :: 'a) \<noteq> rhs \<Longrightarrow> False\<close>\<close>
    val lemma =
      cprop
      |> Goal.init
      |> Clasimp.auto_tac ctxt
      |> Seq.hd
      |> Goal.finish ctxt
  in
    if not (Thm.term_of cprop aconv Thm.prop_of lemma)
      then error "BUG: hclause_of_bool_rw_non_var_rule: lhs and rhs in proved lemma are not equal to those given as arguments. Perhaps a schematic variable has been renamed?"
      else lemma
  end

  fun forall_exists_rw_lemma ctxt predicate is_forall_rw =
    let
      val T = predicate |> Thm.term_of |> fastype_of |> domain_type |> Thm.ctyp_of ctxt
      val P = predicate
    in
      if is_forall_rw then
        \<^instantiate>\<open>P and 'a=T in
          lemma \<open>(\<forall>x. P x) \<noteq> P (SOME x. \<not>P x) \<Longrightarrow> False\<close> by (insert someI[of \<open>\<lambda>x. \<not>P x\<close>], auto)\<close>
      else
        \<^instantiate>\<open>P and 'a=T in
          lemma \<open>(\<exists>x. P x) \<noteq> P (SOME x. P x) \<Longrightarrow> False\<close> by (insert someI[of \<open>P\<close>], auto)\<close>
    end
end
\<close>

end
