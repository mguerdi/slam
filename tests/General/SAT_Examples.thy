(* adapted from: *)

(*  Title:      HOL/ex/SAT_Examples.thy
    Author:     Alwen Tiu, Tjark Weber
    Copyright   2005-2009
*)

section \<open>Examples for proof methods "sat" and "satx"\<close>

theory SAT_Examples
imports "SLAM.slam"
begin

lemma "True"
by slam (* 0 ms *)

lemma "a | ~a"
by slam (* 3 ms *)

lemma "(a | b) & ~a \<Longrightarrow> b"
by slam (* 11 ms *)

lemma "(a & b) | (c & d) \<Longrightarrow> (a & b) | (c & d)"
(*
apply (tactic \<open>CNF.cnf_rewrite_tac @{context} 1\<close>)
*)
by slam (* 38 ms *)

lemma "(a & b) | (c & d) \<Longrightarrow> (a & b) | (c & d)"
(*
apply (tactic \<open>CNF.cnfx_rewrite_tac @{context} 1\<close>)
apply (erule exE | erule conjE)+
*)
by slam (* 40 ms *)

lemma "P=P=P=P=P=P=P=P=P=P"
by slam (* 285 ms *)

lemma "P=P=P=P=P=P=P=P=P=P"
by slam (* 333 ms *)

lemma  "\<And> a b c. a \<or> b \<or> c \<or> d \<Longrightarrow>
e \<or> f \<or> (a & d) \<Longrightarrow>
~(a \<or> (c & ~c)) \<or> b \<Longrightarrow>
~(b & (x \<or> ~x)) \<or> c \<Longrightarrow>
~(d \<or> False) \<or> c \<Longrightarrow>
~(c \<or> (~p & (p \<or> (q & ~q)))) \<Longrightarrow> False"
by slam (* 80 ms *)

lemma  "!! a b c. a \<or> b \<or> c \<or> d \<Longrightarrow>
e \<or> f \<or> (a & d) \<Longrightarrow>
~(a \<or> (c & ~c)) \<or> b \<Longrightarrow>
~(b & (x \<or> ~x)) \<or> c \<Longrightarrow>
~(d \<or> False) \<or> c \<Longrightarrow>
~(c \<or> (~p & (p \<or> (q & ~q)))) \<Longrightarrow> False"
by slam (* 84 ms *)

end
