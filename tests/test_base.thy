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
  fun cant f = (not o Isabelle_Thread.can) f
  fun unit_cant f = if cant f then () else raise General.Fail "Did not raise exception"

  local
    val tokenize = ML_Lex.tokenize_no_range;
    val tokenize_range = ML_Lex.tokenize_range o Input.range_of;
    val tokenize_text = map Antiquote.Text o ML_Lex.tokenize_no_range;

    val bg_expr = tokenize_text "(fn () =>";
    val en_expr = tokenize_text ")";
    fun make_expr a = bg_expr @ a @ en_expr;

    fun parse_cant (_: Proof.context) input =
    ("unit_cant", [make_expr (ML_Lex.read_source input)]);
  in
    val _ = Theory.setup (ML_Antiquotation.special_form \<^binding>\<open>assert_cant\<close> parse_cant)
  end
\<close>

ML \<open>
  val mk = Skip_Proof.make_thm @{theory}
\<close>

end