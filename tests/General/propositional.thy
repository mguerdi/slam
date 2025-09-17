theory propositional

imports "SLAM.slam"

begin

declare [[slam_trace]]

lemma modus_ponens:
  shows "A \<Longrightarrow> (A \<Longrightarrow> B) \<Longrightarrow> B" 
  by (slam)

lemma excluded_middle:
  shows " A \<or> \<not> A"
  by (slam)

lemma modus_tollens:
  shows "\<not> B \<Longrightarrow> (A \<Longrightarrow> B) \<Longrightarrow> \<not> A"
  by (slam)

lemma or_inl:
  shows "A \<Longrightarrow> A \<or> B"
  by (slam)

lemma or_inr:
  shows "B \<Longrightarrow> A \<or> B"
  by (slam)

lemma or_elim:
  shows "A \<or> B \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> C"
  by (slam)

lemma and_intro:
  shows "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
  by (slam)

lemma and_elim:
  shows "A \<and> B \<Longrightarrow> (A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> C"
  by (slam)

(* lemma argo_issue:
  "(C \<noteq> True \<Longrightarrow> B \<noteq> False \<Longrightarrow> A \<noteq> False \<Longrightarrow> False) \<Longrightarrow> (C \<noteq> False \<Longrightarrow> False) \<Longrightarrow> B \<noteq> False \<Longrightarrow> A \<noteq> False \<Longrightarrow> True \<noteq> False \<Longrightarrow> False"
  using [[argo_trace=full]] by argo *)

lemma or_pass_left:
  shows "A \<or> B \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> C \<or> B"
  by (slam)

lemma or_pass_right:
  shows "A \<or> B \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> A \<or> C"
  by (slam)

lemma double_negation_elimination:
  shows "\<not> \<not> A \<Longrightarrow> A"
  by (slam)

end