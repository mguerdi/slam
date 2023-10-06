theory eligibility

imports "test_base"

begin

(* FIXME: this is from debugging example 26 long ago, but since then the kbo has been fixed. *)
ML_val \<open>
  val c = JClause.of_term (@{term_pat "(\<forall>x. ?x x = (p x \<and> q x)) = False \<or> True = False"}, 0)
  (* both ineligible: *)
  val left_eligible = JClause.is_eligible_cpos c 0
  val right_eligible = JClause.is_eligible_cpos c 1
  val lits = #literals c
  (* left is maximal *)
  val is_maximal_left = Jeha_Order.is_maximal JLit.kbo false (nth lits 0) lits
  val is_maximal_right = Jeha_Order.is_maximal JLit.kbo false (nth lits 1) lits
  (* but not strict maximal ?? *)
  val is_strict_maximal_left = Jeha_Order.is_maximal JLit.kbo true (nth lits 0) lits
  val fa_literal = nth lits 0
  val lit_kbo_with_itself = JLit.kbo (fa_literal, fa_literal)
  val is_strict_maximal_in_singleton = Jeha_Order.is_maximal JLit.kbo true fa_literal [fa_literal, nth lits 1]
\<close>

end