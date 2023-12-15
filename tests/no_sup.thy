theory no_sup

imports "test_base"

begin

declare [[jeha_disable_all]]
declare [[jeha_rule_sup]]
declare [[jeha_rule_e_res]]
declare [[jeha_rule_e_fact]]

(* negative test cases *)

lemma no_sup_below_lambda:
  shows "x = y \<Longrightarrow> (\<lambda> z. x) = (\<lambda> z. y)"
  by (jeha) (* compare: eta_expand.thy *)

lemma no_sup_below_forall:
  shows "x = y \<Longrightarrow> (\<forall> z. p x = p y)"
  by (jeha)

lemma no_sup_in_head:
  shows "f = g \<Longrightarrow> f x = g x"
  by (jeha)

end
