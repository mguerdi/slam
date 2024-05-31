theory sup

imports "JEHA.jeha" HOL.HOL

begin

declare [[jeha_trace]]

declare [[jeha_disable_all]]
declare [[jeha_rule_sup]]
declare [[jeha_rule_e_res]]
declare [[jeha_rule_e_fact]]

declare [[jeha_proof_reconstruction]]
declare [[metis_trace]]

lemma transitivity:
  shows "x = y \<Longrightarrow> y = z \<Longrightarrow> x = z"
  by (jeha) (* 59 ms *)

lemma congruence:
  shows "x = y \<Longrightarrow> f x = f y"
  by (jeha) (* 35 ms *)

lemma deep_congruence:
  shows "x = y \<Longrightarrow> v = w  \<Longrightarrow> f (g (h x) w) = f (g (h y) v)"
  by (jeha) (* 71 ms *)

end
