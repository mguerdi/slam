theory eta_expand

imports "SLAM_TEST_BASE.test_base"

begin

declare [[slam_trace]]

declare [[slam_disable_all]]
declare [[slam_rule_sup]]
declare [[slam_rule_e_res]]
declare [[slam_rule_e_fact]]
declare [[slam_rule_arg_cong]]


lemma
  shows "x = y ==> (\<lambda> z. x) = (\<lambda> z . y)"
  (* by metis *) (* works *)
  by (slam ext)

end
