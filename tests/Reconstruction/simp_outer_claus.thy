theory simp_outer_claus

imports JEHA_TEST_BASE.test_base

begin

ML_val \<open>
  (* PosOuterClaus of conjunction *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (\<not> (B \<and> \<not> C)) \<noteq> True \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> B \<noteq> False \<Longrightarrow> C \<noteq> True \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1 }
  val () = \<^assert> (Thm.eq_thm_prop (expected, clausified))
\<close>

ML_val \<open>
  (* NegOuterClaus of conjunction *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (\<not> (B \<and> \<not> C)) \<noteq> False \<Longrightarrow> D \<Longrightarrow> False"}
  val expected1 = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> B \<noteq> True \<Longrightarrow> False"}
  val expected2 = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> C \<noteq> False \<Longrightarrow> False"}
  val [clausified1, clausified2] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1 }
  val () = \<^assert> (Thm.eq_thm_prop (expected1, clausified1))
  val () = \<^assert> (Thm.eq_thm_prop (expected2, clausified2))
\<close>

ML_val \<open>
  (* PosOuterClaus of disjunction *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (\<not> (B \<or> \<not> C)) \<noteq> True \<Longrightarrow> D \<Longrightarrow> False"}
  val expected1 = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> B \<noteq> False \<Longrightarrow> False"}
  val expected2 = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> C \<noteq> True \<Longrightarrow> False"}
  val [clausified1, clausified2] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1 }
  val () = \<^assert> (Thm.eq_thm_prop (expected1, clausified1))
  val () = \<^assert> (Thm.eq_thm_prop (expected2, clausified2))
\<close>

ML_val \<open>
  (* NegOuterClaus of disjunction *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (\<not> (B \<or> \<not> C)) \<noteq> False \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> B \<noteq> True \<Longrightarrow> C \<noteq> False \<Longrightarrow> D \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1 }
  (* val () = \<^assert> (Thm.eq_thm_prop (expected, clausified)) *)
\<close>

find_theorems "\<not>?A \<or> ?B \<Longrightarrow> ?A \<longrightarrow> ?B"

ML_val \<open>
  (* PosOuterClaus of implication *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (\<not> (B \<longrightarrow> \<not> C)) \<noteq> True \<Longrightarrow> D \<Longrightarrow> False"}
  val expected1 = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> B \<noteq> True \<Longrightarrow> False"}
  val expected2 = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> C \<noteq> True \<Longrightarrow> False"}
  val [clausified1, clausified2] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1 }
  val () = \<^assert> (Thm.eq_thm_prop (expected1, clausified1))
  val () = \<^assert> (Thm.eq_thm_prop (expected2, clausified2))
\<close>

ML_val \<open>
  (* NegOuterClaus of implication *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (\<not> (B \<longrightarrow> \<not> C)) \<noteq> False \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> B \<noteq> False \<Longrightarrow> C \<noteq> False \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1 }
  val () = \<^assert> (Thm.eq_thm_prop (expected, clausified))
\<close>

ML_val \<open>
  (* PosOuterClaus of equality *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (b = c) \<noteq> True \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> b \<noteq> c \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1 }
  val () = \<^assert> (Thm.eq_thm_prop (expected, clausified))
\<close>

ML_val \<open>
  (* NegOuterClaus of equality *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (b = c) \<noteq> False \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> b = c \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1 }
  val () = \<^assert> (Thm.eq_thm_prop (expected, clausified))
\<close>

ML_val \<open>
  (* PosOuterClaus of inequality *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (b \<noteq> c) \<noteq> True \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> b = c \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1 }
  val () = \<^assert> (Thm.eq_thm_prop (expected, clausified))
\<close>

ML_val \<open>
  (* NegOuterClaus of inequality *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (b \<noteq> c) \<noteq> False \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> b \<noteq> c \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1 }
  val () = \<^assert> (Thm.eq_thm_prop (expected, clausified))
\<close>

ML_val \<open>
  val C = mk @{prop "((a = b) \<and> c) \<noteq> False \<Longrightarrow> False"}
  val expected = mk @{prop "a = b \<Longrightarrow> c \<noteq> False \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 0 }
  val () = \<^assert> (Thm.eq_thm_prop (expected, clausified))
\<close>

(* Integration tests *)

declare [[jeha_disable_all]]
declare [[jeha_rule_simp_outer_claus, jeha_rule_sup, jeha_rule_false_elim, jeha_rule_simp_false_elim]]

lemma "(\<not>A \<or> \<not> (B \<longrightarrow> \<not> C)) \<Longrightarrow> A \<Longrightarrow> B"
  using [[jeha_trace]] by jeha

lemma "((a = b) = True) \<Longrightarrow> a \<Longrightarrow> b"
  using [[jeha_trace]] by jeha

end