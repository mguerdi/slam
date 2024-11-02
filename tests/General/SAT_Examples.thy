(* adapted from: *)

(*  Title:      HOL/ex/SAT_Examples.thy
    Author:     Alwen Tiu, Tjark Weber
    Copyright   2005-2009
*)

section \<open>Examples for proof methods "sat" and "satx"\<close>

theory SAT_Examples
imports "JEHA.jeha" Main
begin

declare [[jeha_trace]]

lemma "True"
by jeha (* 0 ms *)

lemma "a | ~a"
by jeha (* 10 ms *)

lemma "(a | b) & ~a \<Longrightarrow> b"
by jeha (* 23 ms *)

lemma "(a & b) | (c & d) \<Longrightarrow> (a & b) | (c & d)"
(*
apply (tactic {* CNF.cnf_rewrite_tac @{context} 1 *})
*)
by jeha (* 130 ms *)

lemma "(a & b) | (c & d) \<Longrightarrow> (a & b) | (c & d)"
(*
apply (tactic {* CNF.cnfx_rewrite_tac @{context} 1 *})
apply (erule exE | erule conjE)+
*)
by jeha (* 139 ms *)

lemma "P=P=P=P=P=P=P=P=P=P"
by jeha (* 1609 ms *)

lemma "P=P=P=P=P=P=P=P=P=P"
by jeha (* 1642 ms *)

lemma  "\<And> a b c. a \<or> b \<or> c \<or> d \<Longrightarrow>
e \<or> f \<or> (a & d) \<Longrightarrow>
~(a \<or> (c & ~c)) \<or> b \<Longrightarrow>
~(b & (x \<or> ~x)) \<or> c \<Longrightarrow>
~(d \<or> False) \<or> c \<Longrightarrow>
~(c \<or> (~p & (p \<or> (q & ~q)))) \<Longrightarrow> False"
by jeha (* 747 ms *)

lemma  "!! a b c. a \<or> b \<or> c \<or> d \<Longrightarrow>
e \<or> f \<or> (a & d) \<Longrightarrow>
~(a \<or> (c & ~c)) \<or> b \<Longrightarrow>
~(b & (x \<or> ~x)) \<or> c \<Longrightarrow>
~(d \<or> False) \<or> c \<Longrightarrow>
~(c \<or> (~p & (p \<or> (q & ~q)))) \<Longrightarrow> False"
by jeha (* 435 ms *)

end
