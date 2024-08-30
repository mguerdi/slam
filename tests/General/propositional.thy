theory propositional

imports "JEHA.jeha"

begin

declare [[jeha_trace]]
declare [[jeha_proof_reconstruction=argo]]
declare [[metis_trace]]

lemma modus_ponens:
  shows "A \<Longrightarrow> (A \<Longrightarrow> B) \<Longrightarrow> B" 
  by (jeha)

lemma excluded_middle:
  shows " A \<or> \<not> A"
  by (jeha)

lemma modus_tollens:
  shows "\<not> B \<Longrightarrow> (A \<Longrightarrow> B) \<Longrightarrow> \<not> A"
  by (jeha)

lemma or_inl:
  shows "A \<Longrightarrow> A \<or> B"
  by (jeha)

lemma or_inr:
  shows "B \<Longrightarrow> A \<or> B"
  by (jeha)

lemma or_elim:
  shows "A \<or> B \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> C"
  by (jeha)

lemma and_intro:
  shows "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
  by (jeha)

lemma and_elim:
  shows "A \<and> B \<Longrightarrow> (A \<Longrightarrow> B \<Longrightarrow> C) \<Longrightarrow> C"
  using [[show_types=false, argo_trace=full]] by (jeha)

lemma or_pass_left:
  shows "A \<or> B \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> C \<or> B"
  by (jeha)

lemma or_pass_right:
  shows "A \<or> B \<Longrightarrow> (B \<Longrightarrow> C) \<Longrightarrow> A \<or> C"
  by (jeha)

lemma double_negation_elimination:
  shows "\<not> \<not> A \<Longrightarrow> A"
  by (jeha)

end