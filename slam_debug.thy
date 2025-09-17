theory slam_debug
  imports Main (* HOL.Hilbert_Choice *)
begin

declare [[ML_exception_trace]]

ML_file_debug \<open>slam_common.ML\<close>
ML_file_debug \<open>clause_id.ML\<close>
ML_file_debug \<open>jterm.ML\<close>
ML_file_debug \<open>slam_order_reference.ML\<close>
ML_file_debug \<open>slam_order.ML\<close>
ML_file_debug \<open>jlit.ML\<close>
ML_file_debug \<open>jclause_pos.ML\<close>
ML_file_debug \<open>slam_log.ML\<close>
ML_file_debug \<open>jclause.ML\<close>
ML_file_debug \<open>slam_proof.ML\<close>
ML_file_debug \<open>slam_unify.ML\<close>
ML_file_debug \<open>slam_subsumption.ML\<close>
ML_file_debug \<open>slam_simplify.ML\<close>
ML_file_debug \<open>slam.ML\<close>
ML_file_debug \<open>slam_tactic.ML\<close>

end
