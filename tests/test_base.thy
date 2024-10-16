theory test_base
  imports JEHA.jeha (* SpecCheck.SpecCheck *)
begin

text \<open>SpecCheck term generators, etc.\<close>

(* ML_file \<open>test_base.ML\<close> *)

(* Antiquotations for term and type patterns from the cookbook. *)
setup \<open>Jeha_Common.term_pat_setup\<close>
setup \<open>Jeha_Common.term_schem_setup\<close>
setup \<open>Jeha_Common.type_pat_setup\<close>

ML \<open>
  fun cant f x = (not oo Basics.can) f x
  fun report cant = if cant then () else raise General.Fail "Did not raise exception"
  val _ = Theory.setup (ML_Antiquotation.special_form \<^binding>\<open>assert_cant\<close> "() |> (report oo cant)")
\<close>

ML \<open>
  val mk = Skip_Proof.make_thm @{theory}
\<close>

end