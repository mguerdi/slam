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
declare [[jeha_proof_reconstruction]]

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
using [[ jeha_proof_reconstruction = false ]] by jeha (* 1642 ms *)

lemma  "!! a b c. [| a | b | c | d ;
e | f | (a & d) ;
~(a | (c & ~c)) | b ;
~(b & (x | ~x)) | c ;
~(d | False) | c ;
~(c | (~p & (p | (q & ~q)))) |] ==> False"
by jeha (* 747 ms *)

lemma  "!! a b c. [| a | b | c | d ;
e | f | (a & d) ;
~(a | (c & ~c)) | b ;
~(b & (x | ~x)) | c ;
~(d | False) | c ;
~(c | (~p & (p | (q & ~q)))) |] ==> False"
by jeha (* 435 ms *)

end
