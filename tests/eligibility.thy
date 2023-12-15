theory eligibility

imports "test_base"

begin

(* old KBO bug *)
ML_val \<open>
  val c = JClause.of_term (@{term_pat "(\<forall>x. ?x x = (p x \<and> q x)) = False \<or> True = False"}, 0);

  val left_eligible = JClause.is_eligible_cpos c 0;
  \<^assert> (left_eligible);

  val right_eligible = JClause.is_eligible_cpos c 1;
  \<^assert> (not right_eligible);

  val lits = #literals c;

  val is_maximal_left = Jeha_Order.is_maximal JLit.kbo false (nth lits 0) lits;
  \<^assert> is_maximal_left;

  val is_maximal_right = Jeha_Order.is_maximal JLit.kbo false (nth lits 1) lits;
  \<^assert> (not is_maximal_right);

  val is_strict_maximal_left = Jeha_Order.is_maximal JLit.kbo true (nth lits 0) lits;
  \<^assert> is_strict_maximal_left;

  val lit_kbo_with_itself = JLit.kbo (nth lits 0, nth lits 0);
  \<^assert> (SOME EQUAL = lit_kbo_with_itself);

  val is_strict_maximal_in_singleton =
    Jeha_Order.is_maximal JLit.kbo true (nth lits 0) [nth lits 0, nth lits 1];
  \<^assert> is_strict_maximal_in_singleton;
\<close>

(* assumes alphabetical ordering of free variables *)
ML \<open>
  val c = JClause.of_term (@{term "x \<noteq> z"}, ~1);
  val x_eligible = JClause.is_eligible_full_pos c ([], JLit.Left, 0);
  val z_eligible = JClause.is_eligible_full_pos c ([], JLit.Right, 0);
  (* x < z alphabetically *)
  \<^assert> (not x_eligible);
  \<^assert> z_eligible;
\<close>


(* eligible: direct subterms of fully applied equality *)
ML_val \<open>
  val t = @{term "x = y"};
  (* x \<not>\<le> y alphabetically but y < x *)
  \<^assert> (JClause.is_eligible_tpos t [2]);
  \<^assert> (not (JClause.is_eligible_tpos t [1]));
\<close>

(* eligible: direct subterms of fully applied inequality *)
ML_val \<open>
  val t = @{term "x \<noteq> y"};
  (* x \<not>\<le> y alphabetically but y < x *)
  \<^assert> (JClause.is_eligible_tpos t [1, 2]);
  \<^assert> (not (JClause.is_eligible_tpos t [1, 1]));
\<close>

(* not eligbile: subterms of partially applied equality *)
ML_val \<open>
  val t = @{term "(=) x"};
  \<^assert> (not (JClause.is_eligible_tpos t [1]));
\<close>

(* not eligbile: subterms of partially applied inequality *)
(* Problem: There is no such thing as a partially applied inequality in Isabelle.
  Possibilities
  * (\<not> \<circ> =) x
  * \<lambda>x. \<not> (x = y) but this would never be eligible because it has no green subterms *)

(* eligible: equality in fully applied inequality *)
(* This recovers the s \<noteq> t condition of (E4) via an application of (E3) with head (\<not>). *)
ML_val \<open>
  val t = @{term "x \<noteq> y"};
  \<^assert> (JClause.is_eligible_tpos t [1]);
\<close>

end