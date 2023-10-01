theory sup

imports "../jeha_debug" HOL.HOL

begin

declare [[jeha_trace]]

declare [[jeha_disable_all]]
declare [[jeha_rule_sup]]
declare [[jeha_rule_e_res]]

declare [[jeha_proof_reconstruction]]
declare [[metis_trace]]

(* positive test cases *)

lemma transitivity:
  shows "x = y \<Longrightarrow> y = z \<Longrightarrow> x = z"
  by (jeha)

lemma congruence:
  shows "x = y \<Longrightarrow> f x = f y"
  by (jeha)

lemma deep_congruence:
  shows "x = y \<Longrightarrow> v = w  \<Longrightarrow> f (g (h x) w) = f (g (h y) v)"
  by (jeha)

(* negative test cases *)

lemma no_sup_below_lambda:
  shows "x = y \<Longrightarrow> (\<lambda> z. x) = (\<lambda> z. y)"
  by (jeha)

lemma no_sup_below_forall:
  shows "x = y \<Longrightarrow> (\<forall> z. p x = p y)"
  by (jeha)

lemma no_sup_in_head:
  shows "f = g \<Longrightarrow> f x = g x"
  by (jeha)


ML \<open>
  val c = JClause.of_term (@{term "x \<noteq> z"}, ~1)
  val x_eligible = JClause.is_eligible_full_pos c ([], JLit.Left, 0)
  val z_eligible = JClause.is_eligible_full_pos c ([], JLit.Right, 0)
\<close>

(*
Sup: 4671:y = z (Axiom) into 4672:x \<noteq> z (Axiom) 
Sup: z ?= z 
Sup: u eligible=true 
Sup: tt' eligible=true 
c_comp_d SOME LESS 
t_comp_t' SOME GREATER 

\<not>(C\<sigma> \<lesssim> D\<sigma>) \<Longleftrightarrow> \<not>(x \<noteq> z \<lesssim> y = z)

{{x, \<bottom>}, {z, \<bottom>}} < {{y}, {z}}

with \<bottom> < x < y < z

*)

ML \<open>
  val ms_ms_int_ord = Jeha_Order.mk_multiset_order_of_strict (Jeha_Order.mk_multiset_order_of_strict (SOME o int_ord))
  val (l, r) = ([[1, 0], [3, 0]], [[2], [3]])
  val b = ms_ms_int_ord (l, r)
  val int_list_eq = Jeha_Order.multiset_eq op=
  val int_list_g = Jeha_Order.multiset_is_greater_reference op= op>
  val int_list_list_g = Jeha_Order.multiset_is_greater_reference int_list_g int_list_eq
  val b' = int_list_list_g (l, r)
\<close>



end