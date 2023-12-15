(*  Title:      HOL/Metis_Examples/Sets.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Metis example featuring typed set theory.
*)

section \<open>Metis Example Featuring Typed Set Theory\<close>

theory Sets
imports "../jeha" Main
begin

declare [[metis_new_skolem]]

lemma "\<exists>x X. \<forall>y. \<exists>z Z. (~P(y,y) | P(x,x) | ~S(z,x)) &
               (S(x,y) | ~S(y,z) | Q(Z,Z))  &
               (Q(X,y) | ~Q(y,Z) | S(X,X))"
by jeha

lemma "P(n::nat) ==> \<not>P(0) ==> n \<noteq> 0"
by jeha

sledgehammer_params [isar_proofs, compress = 1]

(*multiple versions of this example*)
lemma (*equal_union: *)
   "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
proof -
  have F1: "\<forall>(x\<^sub>2::'b set) x\<^sub>1::'b set. x\<^sub>1 \<subseteq> x\<^sub>1 \<union> x\<^sub>2" by (jeha Un_commute Un_upper2)
  have F2a: "\<forall>(x\<^sub>2::'b set) x\<^sub>1::'b set. x\<^sub>1 \<subseteq> x\<^sub>2 \<longrightarrow> x\<^sub>2 = x\<^sub>2 \<union> x\<^sub>1" by (jeha Un_commute subset_Un_eq)
  have F2: "\<forall>(x\<^sub>2::'b set) x\<^sub>1::'b set. x\<^sub>1 \<subseteq> x\<^sub>2 \<and> x\<^sub>2 \<subseteq> x\<^sub>1 \<longrightarrow> x\<^sub>1 = x\<^sub>2" by (jeha F2a subset_Un_eq)
  { assume "\<not> Z \<subseteq> X"
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_upper2) }
  moreover
  { assume AA1: "Y \<union> Z \<noteq> X"
    { assume "\<not> Y \<subseteq> X"
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha F1) }
    moreover
    { assume AAA1: "Y \<subseteq> X \<and> Y \<union> Z \<noteq> X"
      { assume "\<not> Z \<subseteq> X"
        hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_upper2) }
      moreover
      { assume "(Z \<subseteq> X \<and> Y \<subseteq> X) \<and> Y \<union> Z \<noteq> X"
        hence "Y \<union> Z \<subseteq> X \<and> X \<noteq> Y \<union> Z" by (jeha Un_subset_iff)
        hence "Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> Y \<union> Z" by (jeha F2)
        hence "\<exists>x\<^sub>1::'a set. Y \<subseteq> x\<^sub>1 \<union> Z \<and> Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> x\<^sub>1 \<union> Z" by (jeha F1)
        hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_upper2) }
      ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha AAA1) }
    ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha AA1) }
  moreover
  { assume "\<exists>x\<^sub>1::'a set. (Z \<subseteq> x\<^sub>1 \<and> Y \<subseteq> x\<^sub>1) \<and> \<not> X \<subseteq> x\<^sub>1"
    { assume "\<not> Y \<subseteq> X"
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha F1) }
    moreover
    { assume AAA1: "Y \<subseteq> X \<and> Y \<union> Z \<noteq> X"
      { assume "\<not> Z \<subseteq> X"
        hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_upper2) }
      moreover
      { assume "(Z \<subseteq> X \<and> Y \<subseteq> X) \<and> Y \<union> Z \<noteq> X"
        hence "Y \<union> Z \<subseteq> X \<and> X \<noteq> Y \<union> Z" by (jeha Un_subset_iff)
        hence "Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> Y \<union> Z" by (jeha F2)
        hence "\<exists>x\<^sub>1::'a set. Y \<subseteq> x\<^sub>1 \<union> Z \<and> Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> x\<^sub>1 \<union> Z" by (jeha F1)
        hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_upper2) }
      ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha AAA1) }
    ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by blast }
  moreover
  { assume "\<not> Y \<subseteq> X"
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha F1) }
  ultimately show "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by jeha
qed

sledgehammer_params [isar_proofs, compress = 2]

lemma (*equal_union: *)
   "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
proof -
  have F1: "\<forall>(x\<^sub>2::'b set) x\<^sub>1::'b set. x\<^sub>1 \<subseteq> x\<^sub>2 \<and> x\<^sub>2 \<subseteq> x\<^sub>1 \<longrightarrow> x\<^sub>1 = x\<^sub>2" by (jeha Un_commute subset_Un_eq)
  { assume AA1: "\<exists>x\<^sub>1::'a set. (Z \<subseteq> x\<^sub>1 \<and> Y \<subseteq> x\<^sub>1) \<and> \<not> X \<subseteq> x\<^sub>1"
    { assume AAA1: "Y \<subseteq> X \<and> Y \<union> Z \<noteq> X"
      { assume "\<not> Z \<subseteq> X"
        hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_upper2) }
      moreover
      { assume "Y \<union> Z \<subseteq> X \<and> X \<noteq> Y \<union> Z"
        hence "\<exists>x\<^sub>1::'a set. Y \<subseteq> x\<^sub>1 \<union> Z \<and> Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> x\<^sub>1 \<union> Z" by (jeha F1 Un_commute Un_upper2)
        hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_upper2) }
      ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha AAA1 Un_subset_iff) }
    moreover
    { assume "\<not> Y \<subseteq> X"
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_commute Un_upper2) }
    ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha AA1 Un_subset_iff) }
  moreover
  { assume "\<not> Z \<subseteq> X"
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_upper2) }
  moreover
  { assume "\<not> Y \<subseteq> X"
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_commute Un_upper2) }
  moreover
  { assume AA1: "Y \<subseteq> X \<and> Y \<union> Z \<noteq> X"
    { assume "\<not> Z \<subseteq> X"
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_upper2) }
    moreover
    { assume "Y \<union> Z \<subseteq> X \<and> X \<noteq> Y \<union> Z"
      hence "\<exists>x\<^sub>1::'a set. Y \<subseteq> x\<^sub>1 \<union> Z \<and> Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> x\<^sub>1 \<union> Z" by (jeha F1 Un_commute Un_upper2)
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_upper2) }
    ultimately have "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha AA1 Un_subset_iff) }
  ultimately show "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by jeha
qed

sledgehammer_params [isar_proofs, compress = 3]

lemma (*equal_union: *)
   "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
proof -
  have F1a: "\<forall>(x\<^sub>2::'b set) x\<^sub>1::'b set. x\<^sub>1 \<subseteq> x\<^sub>2 \<longrightarrow> x\<^sub>2 = x\<^sub>2 \<union> x\<^sub>1" by (jeha Un_commute subset_Un_eq)
  have F1: "\<forall>(x\<^sub>2::'b set) x\<^sub>1::'b set. x\<^sub>1 \<subseteq> x\<^sub>2 \<and> x\<^sub>2 \<subseteq> x\<^sub>1 \<longrightarrow> x\<^sub>1 = x\<^sub>2" by (jeha F1a subset_Un_eq)
  { assume "(Z \<subseteq> X \<and> Y \<subseteq> X) \<and> Y \<union> Z \<noteq> X"
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha F1 Un_commute Un_subset_iff Un_upper2) }
  moreover
  { assume AA1: "\<exists>x\<^sub>1::'a set. (Z \<subseteq> x\<^sub>1 \<and> Y \<subseteq> x\<^sub>1) \<and> \<not> X \<subseteq> x\<^sub>1"
    { assume "(Z \<subseteq> X \<and> Y \<subseteq> X) \<and> Y \<union> Z \<noteq> X"
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha F1 Un_commute Un_subset_iff Un_upper2) }
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha AA1 Un_commute Un_subset_iff Un_upper2) }
  ultimately show "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_commute Un_upper2)
qed

sledgehammer_params [isar_proofs, compress = 4]

lemma (*equal_union: *)
   "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
proof -
  have F1: "\<forall>(x\<^sub>2::'b set) x\<^sub>1::'b set. x\<^sub>1 \<subseteq> x\<^sub>2 \<and> x\<^sub>2 \<subseteq> x\<^sub>1 \<longrightarrow> x\<^sub>1 = x\<^sub>2" by (jeha Un_commute subset_Un_eq)
  { assume "\<not> Y \<subseteq> X"
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_commute Un_upper2) }
  moreover
  { assume AA1: "Y \<subseteq> X \<and> Y \<union> Z \<noteq> X"
    { assume "\<exists>x\<^sub>1::'a set. Y \<subseteq> x\<^sub>1 \<union> Z \<and> Y \<union> Z \<noteq> X \<and> \<not> X \<subseteq> x\<^sub>1 \<union> Z"
      hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_upper2) }
    hence "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha AA1 F1 Un_commute Un_subset_iff Un_upper2) }
  ultimately show "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V::'a set. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))" by (jeha Un_subset_iff Un_upper2)
qed

sledgehammer_params [isar_proofs, compress = 1]

lemma (*equal_union: *)
   "(X = Y \<union> Z) = (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
by (jeha Un_least Un_upper1 Un_upper2 set_eq_subset)

lemma "(X = Y \<inter> Z) = (X \<subseteq> Y \<and> X \<subseteq> Z \<and> (\<forall>V. V \<subseteq> Y \<and> V \<subseteq> Z \<longrightarrow> V \<subseteq> X))"
by (jeha Int_greatest Int_lower1 Int_lower2 subset_antisym)

lemma fixedpoint: "\<exists>!x. f (g x) = x \<Longrightarrow> \<exists>!y. g (f y) = y"
by jeha

lemma (* fixedpoint: *) "\<exists>!x. f (g x) = x \<Longrightarrow> \<exists>!y. g (f y) = y"
proof -
  assume "\<exists>!x::'a. f (g x) = x"
  thus "\<exists>!y::'b. g (f y) = y" by jeha
qed

lemma (* singleton_example_2: *)
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
by (jeha Set.subsetI Union_upper insertCI set_eq_subset)

lemma (* singleton_example_2: *)
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
by (jeha Set.subsetI Union_upper insert_iff set_eq_subset)

lemma singleton_example_2:
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
proof -
  assume "\<forall>x \<in> S. \<Union>S \<subseteq> x"
  hence "\<forall>x\<^sub>1. x\<^sub>1 \<subseteq> \<Union>S \<and> x\<^sub>1 \<in> S \<longrightarrow> x\<^sub>1 = \<Union>S" by (jeha set_eq_subset)
  hence "\<forall>x\<^sub>1. x\<^sub>1 \<in> S \<longrightarrow> x\<^sub>1 = \<Union>S" by (jeha Union_upper)
  hence "\<forall>x\<^sub>1::('a set) set. \<Union>S \<in> x\<^sub>1 \<longrightarrow> S \<subseteq> x\<^sub>1" by (jeha subsetI)
  hence "\<forall>x\<^sub>1::('a set) set. S \<subseteq> insert (\<Union>S) x\<^sub>1" by (jeha insert_iff)
  thus "\<exists>z. S \<subseteq> {z}" by jeha
qed

text \<open>
  From W. W. Bledsoe and Guohui Feng, SET-VAR. JAR 11 (3), 1993, pages
  293-314.
\<close>

(* Notes: (1) The numbering doesn't completely agree with the paper.
   (2) We must rename set variables to avoid type clashes. *)
lemma "\<exists>B. (\<forall>x \<in> B. x \<le> (0::int))"
      "D \<in> F \<Longrightarrow> \<exists>G. \<forall>A \<in> G. \<exists>B \<in> F. A \<subseteq> B"
      "P a \<Longrightarrow> \<exists>A. (\<forall>x \<in> A. P x) \<and> (\<exists>y. y \<in> A)"
      "a < b \<and> b < (c::int) \<Longrightarrow> \<exists>B. a \<notin> B \<and> b \<in> B \<and> c \<notin> B"
      "P (f b) \<Longrightarrow> \<exists>s A. (\<forall>x \<in> A. P x) \<and> f s \<in> A"
      "P (f b) \<Longrightarrow> \<exists>s A. (\<forall>x \<in> A. P x) \<and> f s \<in> A"
      "\<exists>A. a \<notin> A"
      "(\<forall>C. (0, 0) \<in> C \<and> (\<forall>x y. (x, y) \<in> C \<longrightarrow> (Suc x, Suc y) \<in> C) \<longrightarrow> (n, m) \<in> C) \<and> Q n \<longrightarrow> Q m"
       apply (jeha all_not_in_conv)
      apply (jeha all_not_in_conv)
     apply (jeha mem_Collect_eq)
    apply (jeha less_le singleton_iff)
   apply (jeha mem_Collect_eq)
  apply (jeha mem_Collect_eq)
 apply (jeha all_not_in_conv)
by (jeha pair_in_Id_conv)

end
