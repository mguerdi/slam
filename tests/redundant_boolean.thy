theory redundant_boolean

imports "../jeha"

begin

ML_val \<open>
  val t =
    JClause.of_term
      (@{term "True \<noteq> False \<or> (False \<longrightarrow> True) = True \<or> (True \<longrightarrow> False) = True"}, 0);
\<close>

end