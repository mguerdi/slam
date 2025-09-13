theory SMT_Examples

imports "SLAM.slam" Complex_Main

begin

declare [[slam_trace]]

section \<open>Propositional and first-order logic\<close>

lemma "True" by slam
lemma "p \<or> \<not>p" by slam
lemma "(p \<and> True) = p" by slam
lemma "(p \<or> q) \<and> \<not>p \<Longrightarrow> q" by slam
lemma "(a \<and> b) \<or> (c \<and> d) \<Longrightarrow> (a \<and> b) \<or> (c \<and> d)" by slam
lemma "(p1 \<and> p2) \<or> p3 \<longrightarrow> (p1 \<longrightarrow> (p3 \<and> p2) \<or> (p1 \<and> p3)) \<or> p1" by slam
lemma "P = P = P = P = P = P = P = P = P = P" by slam

lemma
  assumes "a \<or> b \<or> c \<or> d"
      and "e \<or> f \<or> (a \<and> d)"
      and "\<not> (a \<or> (c \<and> ~c)) \<or> b"
      and "\<not> (b \<and> (x \<or> \<not> x)) \<or> c"
      and "\<not> (d \<or> False) \<or> c"
      and "\<not> (c \<or> (\<not> p \<and> (p \<or> (q \<and> \<not> q))))"
  shows False
  using assms by slam

axiomatization symm_f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  symm_f: "symm_f x y = symm_f y x"

lemma "a = a \<and> symm_f a b = symm_f b a"
  by (slam symm_f)

lemma "\<forall>x::int. P x \<longrightarrow> (\<forall>y::int. P x \<or> P y)"
  by slam

lemma
  assumes "(\<forall>x y. P x y = x)"
  shows "(\<exists>y. P x y) = P x c"
  using assms by slam

lemma
  assumes "(\<forall>x y. P x y = x)"
  and "(\<forall>x. \<exists>y. P x y) = (\<forall>x. P x c)"
  shows "(\<exists>y. P x y) = P x c"
  using assms by slam 

lemma
  assumes "if P x then \<not>(\<exists>y. P y) else (\<forall>y. \<not>P y)"
  shows "P x \<longrightarrow> P y"
  (* using assms by slam (* FIXME: doesn't work *) *)
  sorry

(* From HOL/*)

lemma "(\<forall>x. P x) \<or> \<not> All P"
by slam

end