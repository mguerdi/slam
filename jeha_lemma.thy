theory jeha_lemma

imports HOL.Hilbert_Choice HOL.Transfer

begin

datatype 'a type_arg_wrapper = Skolem_Type_Arg (inner: "'a itself")

term "Skolem_Type_Arg TYPE(bool)"

ML_val \<open>
  val t = @{term "Skolem_Type_Arg"}
  val c = @{const Skolem_Type_Arg(bool)}
\<close>

(* from SMT.thy *)
lemma verit_sko_forall: \<open>(\<forall>x. P x) \<longleftrightarrow> P (SOME x. \<not>P x)\<close>
  by (insert someI[of \<open>\<lambda>x. \<not>P x\<close>], auto)

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
  val forall_exists_rw_lemma: Proof.context -> term -> bool -> term * term * term -> thm
  val neg_ext_lemma: Proof.context -> term * term -> term * term * term -> thm
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

  (* Turn P with schematic vars ?x\<^sub>1, \<dots>, ?x\<^sub>n into \<lambda>x\<^sub>1 \<dots> x\<^sub>n. P [?x\<^sub>1:=x\<^sub>1, \<dots>?x\<^sub>n:=x\<^sub>n]. *)
  fun abstract_over_schematic_vars predicate =
    error "abstract_over_schematic_vars unimplemented"

  (* FIXME: Pass skolem prem (HOLogic.mk_eq \<dots>) and sk_with_args only? But that makes a manual
  proof (without fast) harder / impossible. *)
  fun forall_exists_rw_lemma ctxt predicate is_forall_rw (sk, sk_with_args, sk_def) =
    let
      val T = predicate |> fastype_of |> domain_type
      val P = predicate
      val skT = fastype_of sk
      (* FIXME: Question: does `instantiate lemma \<dots>` prove first and then instantiate or the other
      way around. *)
      val prop = 
        if is_forall_rw then
          \<^instantiate>\<open>'skT = skT and sk and sk_def and sk_with_args and P and 'a=T in
            prop \<open>(sk :: 'skT) = sk_def \<Longrightarrow> (\<forall>x :: 'a. P x) \<noteq> P sk_with_args \<Longrightarrow> False\<close>\<close>
        else
          \<^instantiate>\<open>'skT = skT and sk and sk_def and sk_with_args and P and 'a=T in
            prop \<open>(sk :: 'skT) = sk_def \<Longrightarrow> (\<exists>x :: 'a. P x) \<noteq> P sk_with_args \<Longrightarrow> False\<close>\<close>
      val th =
        prop
        |> Thm.cterm_of ctxt
        |> Goal.init
        |> fast_tac ctxt 1
        |> Seq.hd
        |> Goal.finish ctxt
    in
      th 
    end

  fun neg_ext_lemma ctxt (s, s') (sk, sk_with_args, sk_def) =
    let
      val skT = fastype_of sk
      val (dom, codom) = dest_funT (fastype_of s)
      val prop = \<^instantiate>\<open>
        'skT = skT and sk and sk_def and sk_with_args and s and s' and 'a=dom and 'b=codom in
        prop \<open>
          (sk :: 'skT) = sk_def
          \<Longrightarrow> (s :: 'a \<Rightarrow> 'b) sk_with_args = s' sk_with_args
          \<Longrightarrow> s = s'\<close>\<close>
      (* FIXME: Where does instantiate get its proof context from? Or is that not necessary for type
      checking terms? *)
      val term_hint = \<^instantiate>\<open>
        s and s' and 'a=dom and 'b=codom in term \<open>\<lambda>uub. (s :: 'a \<Rightarrow> 'b) uub \<noteq> s' uub\<close>\<close>
      val P = Thm.cterm_of ctxt term_hint
      val dom = Thm.ctyp_of ctxt dom
      val lemma_lemma = \<^instantiate>\<open>
        P and 'a=dom in lemma \<open>\<exists>x :: 'a. P x \<Longrightarrow> P (SOME x. P x)\<close> by (insert someI_ex)\<close>
      val th =
        prop
        |> Thm.cterm_of ctxt
        |> Goal.init
        |> (
          print_tac ctxt "BEFORE FAST"
          THEN Method.insert_tac ctxt [lemma_lemma] 1
          THEN print_tac ctxt "AFTER_INSERT"
          THEN fast_tac ctxt 1
          THEN print_tac ctxt "AFTER FAST"
        )
        |> Seq.hd
        |> Goal.finish ctxt
    in
      th
    end
end
\<close>

end
