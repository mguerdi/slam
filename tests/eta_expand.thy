theory eta_expand

imports "test_base"

begin

declare [[jeha_trace]]

declare [[jeha_disable_all]]
declare [[jeha_rule_sup]]
declare [[jeha_rule_e_res]]
declare [[jeha_rule_e_fact]]
declare [[jeha_rule_arg_cong]]


lemma
  shows "x = y ==> (\<lambda> z. x) = (\<lambda> z . y)"
  (* by metis *) (* works *)
  by (jeha ext)

end