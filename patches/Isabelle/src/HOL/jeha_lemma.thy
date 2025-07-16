theory jeha_lemma

imports Hilbert_Choice Transfer jeha_base

begin

ML_file \<open>HOL/Tools/jeha_proof_util.ML\<close>

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

lemma forall_hoist_just_to_be_safe:
  "((\<forall>x. P x) = True \<Longrightarrow> (\<forall>x. P x) = False \<Longrightarrow> False) \<equiv> (\<And>x.((\<forall>x. P x) = True \<Longrightarrow> P x = False \<Longrightarrow> False))"
  by auto

lemma not_atomize: "(\<not> A \<Longrightarrow> False) \<equiv> Trueprop A"
  by (cut_tac atomize_not [of "\<not> A"]) simp

lemma discharge_skolem_poc: "((\<And>f. (\<And>x. f x = g x) \<Longrightarrow> P)) \<Longrightarrow> P"
proof -
  have L: "(\<And>x. g x = g x)"
  proof -
    fix x
    show "g x = g x" by (fact HOL.refl)
  qed

  assume A: "\<And>f. (\<And>x. f x = g x) \<Longrightarrow> P"
  then have "(\<And>x. g x = g x) \<Longrightarrow> P" by this
  then show "P"
    apply this
    apply (fact L)
    done
qed

lemma skolemization_rule_ex:
  "c = (SOME z. P z) \<Longrightarrow> (\<exists>z. P z) \<longleftrightarrow> P c"
  using some_eq_ex by auto

lemma skolemization_rule_fa:
  "c = (SOME z. \<not>P z) \<Longrightarrow> (\<forall>z. P z) \<longleftrightarrow> P c"
  using verit_sko_forall[of "P"] by auto

ML\<open>
  (* reduce f x = g to f = (\<lambda>x. g x) *)
  fun lam_tac ctxt i th =
    let
      fun goal_fun (goal, i): tactic =
        let
          val (f, x) =
            goal
            |> Drule.strip_imp_concl
            |> Thm.dest_arg (* remove Trueprop *)
            |> Thm.dest_arg1 (* lhs of equality *)
            |> Thm.dest_comb
          val (aT, bT) = Thm.dest_funT (Thm.ctyp_of_cterm f)
          val fun_cong = \<^instantiate>\<open>f and x and 'a = aT and 'b = bT in
            lemma \<open>\<And>g. f = g \<Longrightarrow> f x = g x\<close> by (rule HOL.fun_cong)\<close>
        in
          resolve_tac ctxt [fun_cong] i
        end
    in
      CSUBGOAL goal_fun i th handle CTERM _ => Seq.empty
    end

  (* reduce f x y \<dots> = g to f = \<lambda>x y \<dots> g x y *)
  fun full_lam_tac ctxt i = REPEAT_DETERM (lam_tac ctxt i)

  (* prove
    sk = (\<lambda>x y \<dots>. SOME z. \<not>P x y \<dots> z) \<Longrightarrow> (\<forall>z. P x y \<dots> z) = P x y \<dots> (sk x y \<dots>)
  or
    sk = (\<lambda>x y \<dots>. SOME z. P x y \<dots> z) \<Longrightarrow> (\<exists>z. P x y \<dots> z) = P x y \<dots> (sk x y \<dots>) *)
  fun fa_ex_rw_lemma_tac ctxt is_forall_rw =
    (* Goal: sk = (\<lambda>x y \<dots>. SOME z. \<not>P x y \<dots> z) \<Longrightarrow> (\<forall>z. P x y \<dots> z) = P x y \<dots> (sk x y \<dots>) *)
    resolve_tac
      ctxt
      (if is_forall_rw then @{thms "skolemization_rule_fa"} else @{thms "skolemization_rule_ex"})
    (* Goal: sk = (\<lambda>x y \<dots>. SOME z. \<not>P x y \<dots> z) \<Longrightarrow> sk x y \<dots> = (SOME z. \<not>P x y \<dots> z) *)
    THEN' full_lam_tac ctxt
    (* Goal: sk = (\<lambda>x y \<dots>. SOME z. \<not>P x y \<dots> z) \<Longrightarrow> sk = (\<lambda>x y \<dots>. SOME z. \<not>P x y \<dots> z) *)
    THEN' assume_tac ctxt

  (* Reduce Q \<Longrightarrow> P to Q = P *)
  fun reduce_to_bool_eq_tac ctxt i th =
    let
      fun goal_fun (goal, i): tactic =
        let
          val Q =
            goal
            |> Drule.strip_imp_prems
            |> (fn prems => nth prems (length prems - 1))
            |> Thm.dest_arg (* remove Trueprop *)
          val tac =
            (* Creates two subgoals: Q \<Longrightarrow> Q and Q = P. *)
            resolve_tac ctxt [\<^instantiate>\<open>Q in lemma \<open>\<And> P. Q = P \<Longrightarrow> Q \<Longrightarrow> P\<close> by (rule HOL.iffD1)\<close>]
            (* Close subgoal Q \<Longrightarrow> Q. *)
            THEN_ALL_NEW (TRY o assume_tac ctxt)
        in
          tac i
        end
    in
      CSUBGOAL goal_fun i th handle CTERM _ => Seq.empty
    end

  (* Prove
    sk = (\<lambda>\<dots>. SOME z. f z \<noteq> g z) \<Longrightarrow> f (sk \<dots>) = g (sk \<dots>) \<Longrightarrow> f = g *)
  fun neg_ext_lemma_tac ctxt =
    (* Goal: sk = (\<lambda>\<dots>. SOME z. f z \<noteq> g z) \<Longrightarrow> f (sk \<dots>) = g (sk \<dots>) \<Longrightarrow> f = g *)
    (*                                                                   ^^^^^^ *)
    resolve_tac ctxt [@{lemma "\<forall>x. f x = g x \<Longrightarrow> f = g" by auto}]
    (* Goal: sk = (\<lambda>\<dots>. SOME z. f z \<noteq> g z) \<Longrightarrow> f (sk \<dots>) = g (sk \<dots>) \<Longrightarrow> \<forall>x. f x = g x *)
    (*                                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)
    THEN' reduce_to_bool_eq_tac ctxt
    (* Goal: sk = (\<lambda>\<dots>. SOME z. f z \<noteq> g z) \<Longrightarrow> (f (sk \<dots>) = g (sk \<dots>)) \<longleftrightarrow> (\<forall>x. f x = g x) *)
    (*                                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)
    THEN' resolve_tac ctxt @{thms HOL.sym}
    (* Goal: sk = (\<lambda>\<dots>. SOME z. f z \<noteq> g z) \<Longrightarrow> (\<forall>x. f x = g x) \<longleftrightarrow> (f (sk \<dots>) = g (sk \<dots>)) *)
    (*                                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)
    THEN' resolve_tac ctxt @{thms skolemization_rule_fa}
    (* Goal: sk = (\<lambda>\<dots>. SOME z. f z \<noteq> g z) \<Longrightarrow> sk \<dots> = (SOME z. f z \<noteq> g z) *)
    (*                                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)
    THEN' full_lam_tac ctxt
    (* Goal: sk = (\<lambda>\<dots>. SOME z. f z \<noteq> g z) \<Longrightarrow> sk = (\<lambda>\<dots>. SOME z. f z \<noteq> g z) *)
    (*       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  *)
    THEN' assume_tac ctxt
\<close>

ML \<open>
signature JEHA_LEMMA =
sig
  (* FIXME: the result of these should really be HClause.hthm *)
  val hclause_of_uninstantiated_bool_rw_rule: Proof.context -> term * term -> thm
  val forall_exists_rw_lemma: Proof.context -> term -> bool -> term * term * term -> thm
  val neg_ext_lemma: Proof.context -> term * term -> term * term * term -> thm
end

structure Jeha_Lemma: JEHA_LEMMA =
struct

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

fun forall_exists_rw_lemma ctxt predicate is_forall_rw (sk, sk_with_args, sk_def) =
  let
    val T = predicate |> fastype_of |> domain_type
    val P = predicate
    val skT = fastype_of sk
    val prop =
      if is_forall_rw then
        \<^instantiate>\<open>'skT = skT and sk and sk_def and sk_with_args and P and 'a=T in
            prop \<open>(sk :: 'skT) = sk_def \<Longrightarrow> (\<forall>x :: 'a. P x) = P sk_with_args\<close>\<close>
      else
        \<^instantiate>\<open>'skT = skT and sk and sk_def and sk_with_args and P and 'a=T in
            prop \<open>(sk :: 'skT) = sk_def \<Longrightarrow> (\<exists>x :: 'a. P x) = P sk_with_args\<close>\<close>
    val th =
      prop
      |> Thm.cterm_of ctxt
      |> Goal.init
      |> Jeha_Proof_Util.with_all_vars_fixed ctxt (HEADGOAL (fa_ex_rw_lemma_tac ctxt is_forall_rw))
      |> Seq.hd
      |> Goal.finish ctxt
  in
    (* Turn into HClause form *)
    Drule.comp_no_flatten (th, Thm.nprems_of th) 1 @{thm HOL.cnf.clause2raw_notE}
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
    val th =
      prop
      |> Thm.cterm_of ctxt
      |> Goal.init
      |> Jeha_Proof_Util.with_all_vars_fixed ctxt (HEADGOAL (neg_ext_lemma_tac ctxt))
      |> Seq.hd
      |> Goal.finish ctxt
  in
    th
  end

end
\<close>

end
