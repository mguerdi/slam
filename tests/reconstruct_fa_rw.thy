theory reconstruct_fa_rw

imports "../jeha"

begin

thm verit_sko_forall

(* from example 26 *)
lemma
  "
  ((\<forall>xa. x xa = (p xa \<and> q xa)) \<noteq> False \<Longrightarrow> False)
  \<Longrightarrow>
  ( ( x (SOME z. x z \<noteq> (p z \<and> q z))
      =
      (p (SOME z. x z \<noteq> (p z \<and> q z)) \<and> q (SOME z. x z \<noteq> (p z \<and> q z))))
    \<noteq> False
  \<Longrightarrow> False)"
  using verit_sko_forall[of "\<lambda> z. x z = (p z \<and> q z)"] by auto

end