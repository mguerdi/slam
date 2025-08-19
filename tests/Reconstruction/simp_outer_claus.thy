theory simp_outer_claus

imports JEHA_TEST_BASE.test_base

begin

ML \<open>
  val mk = mk #> HClause.of_lemma
  val eq = Thm.eq_thm_prop o apply2 HClause.thm_of
\<close>

ML_val \<open>
  (* PosOuterClaus of conjunction *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (\<not> (B \<and> \<not> C)) \<noteq> True \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> B \<noteq> False \<Longrightarrow> C \<noteq> True \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1, quant_info = NONE }
  val () = \<^assert> (eq (expected, clausified))
\<close>

ML_val \<open>
  (* NegOuterClaus of conjunction *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (\<not> (B \<and> \<not> C)) \<noteq> False \<Longrightarrow> D \<Longrightarrow> False"}
  val expected1 = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> B \<noteq> True \<Longrightarrow> False"}
  val expected2 = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> C \<noteq> False \<Longrightarrow> False"}
  val [clausified1, clausified2] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1, quant_info = NONE }
  val () = \<^assert> (eq (expected1, clausified1))
  val () = \<^assert> (eq (expected2, clausified2))
\<close>

ML_val \<open>
  (* PosOuterClaus of disjunction *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (\<not> (B \<or> \<not> C)) \<noteq> True \<Longrightarrow> D \<Longrightarrow> False"}
  val expected1 = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> B \<noteq> False \<Longrightarrow> False"}
  val expected2 = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> C \<noteq> True \<Longrightarrow> False"}
  val [clausified1, clausified2] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1, quant_info = NONE }
  val () = \<^assert> (eq (expected1, clausified1))
  val () = \<^assert> (eq (expected2, clausified2))
\<close>

ML_val \<open>
  (* NegOuterClaus of disjunction *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (\<not> (B \<or> \<not> C)) \<noteq> False \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> B \<noteq> True \<Longrightarrow> C \<noteq> False \<Longrightarrow> D \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1, quant_info = NONE }
  (* val () = \<^assert> (eq (expected, clausified)) *)
\<close>

find_theorems "\<not>?A \<or> ?B \<Longrightarrow> ?A \<longrightarrow> ?B"

ML_val \<open>
  (* PosOuterClaus of implication *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (\<not> (B \<longrightarrow> \<not> C)) \<noteq> True \<Longrightarrow> D \<Longrightarrow> False"}
  val expected1 = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> B \<noteq> True \<Longrightarrow> False"}
  val expected2 = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> C \<noteq> True \<Longrightarrow> False"}
  val [clausified1, clausified2] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1, quant_info = NONE }
  val () = \<^assert> (eq (expected1, clausified1))
  val () = \<^assert> (eq (expected2, clausified2))
\<close>

ML_val \<open>
  (* NegOuterClaus of implication *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (\<not> (B \<longrightarrow> \<not> C)) \<noteq> False \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> B \<noteq> False \<Longrightarrow> C \<noteq> False \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1, quant_info = NONE }
  val () = \<^assert> (eq (expected, clausified))
\<close>

ML_val \<open>
  (* PosOuterClaus of equality *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (b = c) \<noteq> True \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> b \<noteq> c \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1, quant_info = NONE }
  val () = \<^assert> (eq (expected, clausified))
\<close>

ML_val \<open>
  (* NegOuterClaus of equality *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (b = c) \<noteq> False \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> b = c \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1, quant_info = NONE }
  val () = \<^assert> (eq (expected, clausified))
\<close>

ML_val \<open>
  (* PosOuterClaus of inequality *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (b \<noteq> c) \<noteq> True \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> b = c \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1, quant_info = NONE }
  val () = \<^assert> (eq (expected, clausified))
\<close>

ML_val \<open>
  (* NegOuterClaus of inequality *)
  val C = mk @{prop "\<not>A \<Longrightarrow> (b \<noteq> c) \<noteq> False \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mk @{prop "\<not>A \<Longrightarrow> D \<Longrightarrow> b \<noteq> c \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1, quant_info = NONE }
  val () = \<^assert> (eq (expected, clausified))
\<close>

ML_val \<open>
  val C = mk @{prop "((a = b) \<and> c) \<noteq> False \<Longrightarrow> False"}
  val expected = mk @{prop "a = b \<Longrightarrow> c \<noteq> False \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 0, quant_info = NONE }
  val () = \<^assert> (eq (expected, clausified))
\<close>

ML_val \<open>
  val C = mk (@{term_schem
    "(?x::'a \<Rightarrow> 'a) (c::'a) \<noteq> ?x (d::'a) \<Longrightarrow> ((jsk41::('a \<Rightarrow> 'a) \<Rightarrow> 'a) ?x = ?x (?x4::'a)) \<noteq> True \<Longrightarrow> False"})
  val expected = mk (@{term_schem
    "(?x::'a \<Rightarrow> 'a) (c::'a) \<noteq> ?x (d::'a) \<Longrightarrow> (jsk41::('a \<Rightarrow> 'a) \<Rightarrow> 'a) ?x \<noteq> ?x (?x4::'a) \<Longrightarrow> False"})
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 1, quant_info = NONE }
  val () = \<^assert> (eq (expected, clausified))
\<close>

declare [[jeha_trace, show_types]]

(* FIXME: figure out what's happening here *)
ML_val \<open>
  val C = mk @{term_schem "
    False \<noteq> ((?x5::('a \<Rightarrow> 'b) \<Rightarrow> ?'a2) (g::'a \<Rightarrow> 'b) = (?y_eqneqhoist4::('a \<Rightarrow> 'b) \<Rightarrow> ?'a2) g)
    \<Longrightarrow> ?x5 (f::'a \<Rightarrow> 'b) \<noteq> ?y_eqneqhoist4 f
    \<Longrightarrow> False"}
  val expected = mk @{term_schem "
    (?x5::('a \<Rightarrow> 'b) \<Rightarrow> ?'a2) (f::'a \<Rightarrow> 'b) \<noteq> (?y_eqneqhoist4::('a \<Rightarrow> 'b) \<Rightarrow> ?'a2) f
    \<Longrightarrow> ?x5 (g::'a \<Rightarrow> 'b) = ?y_eqneqhoist4 g
    \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 0, quant_info = NONE }
  val () = \<^assert> (eq (expected, clausified))
\<close>

ML_val \<open>
  val C = mk @{term_schem "
    False \<noteq> ((?x5::('a \<Rightarrow> 'b) \<Rightarrow> ?'c) (g::'a \<Rightarrow> 'b) = (?y_eqneqhoist4::('a \<Rightarrow> 'b) \<Rightarrow> ?'c) g)
    \<Longrightarrow> ?x5 (f::'a \<Rightarrow> 'b) \<noteq> ?y_eqneqhoist4 f
    \<Longrightarrow> False"}
  val expected = mk @{term_schem "
    (?x5::('a \<Rightarrow> 'b) \<Rightarrow> ?'c) (f::'a \<Rightarrow> 'b) \<noteq> (?y_eqneqhoist4::('a \<Rightarrow> 'b) \<Rightarrow> ?'c) f
    \<Longrightarrow> ?x5 (g::'a \<Rightarrow> 'b) = ?y_eqneqhoist4 g
    \<Longrightarrow> False"}
  val [clausified] = Jeha_Proof.reconstruct_simp_outer_claus @{context} { premise = C, literal = 0, quant_info = NONE }
  val () = \<^assert> (eq (expected, clausified))
\<close>

(* Integration tests *)

declare [[jeha_disable_all]]
declare [[jeha_rule_simp_outer_claus, jeha_rule_sup, jeha_rule_false_elim, jeha_rule_simp_false_elim]]

lemma "(\<not>A \<or> \<not> (B \<longrightarrow> \<not> C)) \<Longrightarrow> A \<Longrightarrow> B"
  using [[jeha_trace]] by jeha

lemma "((a = b) = True) \<Longrightarrow> a \<Longrightarrow> b"
  using [[jeha_trace]] by jeha

end