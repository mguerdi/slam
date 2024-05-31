theory test_base
  imports JEHA.jeha (* SpecCheck.SpecCheck *)
begin

text \<open>SpecCheck term generators, etc.\<close>

(* ML_file \<open>test_base.ML\<close> *)

(* Antiquotations for term and type patterns from the cookbook. *)
setup \<open>Jeha_Common.term_pat_setup\<close>
setup \<open>Jeha_Common.term_schem_setup\<close>
setup \<open>Jeha_Common.type_pat_setup\<close>

end