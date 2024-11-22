theory jeha_sledgehammer

imports Sledgehammer jeha

begin

ML \<open>
  fun jeha_tac { global_facts, local_facts } ctxt = 
    SELECT_GOAL (Jeha_Tactic.jeha_method ([], global_facts) ctxt local_facts)

  val jeha_method = {
    name = "jeha",
    string_of = "jeha",
    is_proof_method_direct = true, 
    is_proof_method_multi_goal = false,
    needs_insert_local_facts = false,
    needs_insert_global_facts = false,
    tac = jeha_tac,
    try0_priority = 10,
    no_other_try0_methods = true
  }

  val r = Sledgehammer_Proof_Methods.register_dynamic_proof_method jeha_method
\<close>

end