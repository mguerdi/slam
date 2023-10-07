theory jeha_debug
  imports Main (* HOL.Hilbert_Choice *)
begin

declare [[ML_exception_trace]]

ML_file_debug \<open>jeha_common.ML\<close>
ML_file_debug \<open>clause_id.ML\<close>
ML_file_debug \<open>jterm.ML\<close>
ML_file_debug \<open>jeha_order_reference.ML\<close>
ML_file_debug \<open>jeha_order.ML\<close>
ML_file_debug \<open>jlit.ML\<close>
ML_file_debug \<open>jclause_pos.ML\<close>
ML_file_debug \<open>jeha_log.ML\<close>
ML_file_debug \<open>jclause.ML\<close>
ML_file_debug \<open>jeha_proof.ML\<close>
ML_file_debug \<open>jeha_unify.ML\<close>
ML_file_debug \<open>jeha_subsumption.ML\<close>
ML_file_debug \<open>jeha_simplify.ML\<close>
ML_file_debug \<open>jeha.ML\<close>
ML_file_debug \<open>jeha_tactic.ML\<close>

end
