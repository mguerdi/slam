theory vsmetis

imports "../jeha"

begin

lemma "f = g \<Longrightarrow> (\<And>x. f x = g x)"
  by metis

declare [[jeha_trace]]

(* lemma "(\<And>x. f x = g x) \<Longrightarrow> f = g"
  sledgehammer[dont_try0]
  by (jeha) *)

(* declare [[jeha_proof_reconstruction]] *)
declare [[metis_trace]]

thm sum.distrib

lemma "(\<Sum>i\<in>A. i\<^sup>2 + 2 * i + 1) = (\<Sum>i\<in>A. i\<^sup>2) + (\<Sum>i\<in>A. 2 * i) + (\<Sum>i\<in>A. 1)"
  (* sledgehammer [dont_try0] *)
  (* by (metis sum.distrib) (* times out >1s *) *)
  by (jeha sum.distrib) (* works but proof reconstruction takes long *)


end