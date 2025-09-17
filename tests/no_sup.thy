theory no_sup

imports "test_base"

begin

declare [[slam_disable_all]]
declare [[slam_rule_sup]]
declare [[slam_rule_e_res]]
declare [[slam_rule_e_fact]]

(* negative test cases *)

lemma no_sup_below_lambda:
  shows "x = y \<Longrightarrow> (\<lambda> z. x) = (\<lambda> z. y)"
  by (slam) (* compare: eta_expand.thy *)

lemma no_sup_below_forall:
  shows "x = y \<Longrightarrow> (\<forall> z. p x = p y)"
  by (slam)

lemma no_sup_in_head:
  shows "f = g \<Longrightarrow> f x = g x"
  by (slam)

end
