theory jeha
  imports Main (* HOL.Hilbert_Choice *)
begin

(* from SMT.thy *)
lemma verit_sko_forall: \<open>(\<forall>x. P x) \<longleftrightarrow> P (SOME x. \<not>P x)\<close>
  using someI[of \<open>\<lambda>x. \<not>P x\<close>]
  by auto

ML_file \<open>jeha_common.ML\<close>
ML_file \<open>clause_id.ML\<close>
ML_file \<open>jterm.ML\<close>
ML_file \<open>jeha_order_reference.ML\<close>
ML_file \<open>jeha_order.ML\<close>
ML_file \<open>jlit.ML\<close>
ML_file \<open>jclause_pos.ML\<close>
ML_file \<open>jeha_log.ML\<close>
ML_file \<open>jclause.ML\<close>
ML_file \<open>jeha_proof.ML\<close>
ML_file \<open>jeha_unify.ML\<close>
ML_file \<open>jeha_subsumption.ML\<close>
ML_file \<open>jeha_simplify.ML\<close>
ML_file \<open>jeha.ML\<close>
ML_file \<open>jeha_tactic.ML\<close>

end
