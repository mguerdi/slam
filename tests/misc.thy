theory misc

imports "test_base"

begin

declare [[jeha_trace]]

lemma "f = g \<Longrightarrow> (\<And> x. f x = (id o g) x)"
  by (jeha comp_apply id_apply)

declare [[jeha_disable_all]]
declare [[jeha_rule_arg_cong]]
declare [[jeha_rule_sup]]
declare [[jeha_rule_e_res]]

declare [[jeha_proof_reconstruction]]

lemma arg_cong_test:
  shows "g = f \<Longrightarrow> g a = f a"
  (* by jeha *)
(* FIXME: why does this not work? *)
proof -
  (* note [[ ... ]] *)
  have ?thesis by jeha
qed

lemma
  shows "(1 :: nat) + 1 = 2"
  by (jeha (dump) Num.nat_1_add_1)

end