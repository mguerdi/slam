theory jeha
  imports HOL.Transfer HOL.Argo (* HOL.Sledgehammer *) jeha_lemma (* HOL.Hilbert_Choice *)
begin

ML_file \<open>jeha_common.ML\<close>
ML_file \<open>clause_id.ML\<close>
ML_file \<open>jterm.ML\<close>
ML_file \<open>jeha_order_reference.ML\<close>
ML_file \<open>jeha_order.ML\<close>
ML_file \<open>jlit.ML\<close>
ML_file \<open>jclause_pos.ML\<close>
ML_file \<open>jeha_log.ML\<close>
ML_file \<open>jclause.ML\<close>
ML_file \<open>jeha_argo.ML\<close>
ML_file \<open>hclause.ML\<close>
ML_file \<open>jeha_proof.ML\<close>
ML_file \<open>jeha_unify.ML\<close>
ML_file \<open>jeha_subsumption.ML\<close>
ML_file \<open>jeha_simplify.ML\<close>
ML_file \<open>jeha.ML\<close>
ML_file \<open>jeha_tactic.ML\<close>

end
