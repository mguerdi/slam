theory positive_simplify_reflect

imports JEHA.jeha

begin

lemma "a = b \<Longrightarrow> u a c \<noteq> u b c \<or> C \<Longrightarrow> C"
  using [[jeha_trace, jeha_disable_all,
        jeha_rule_positive_simplify_reflect, jeha_rule_sup, jeha_rule_false_elim]]
  by jeha

end