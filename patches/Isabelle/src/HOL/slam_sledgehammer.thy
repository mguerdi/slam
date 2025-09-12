theory slam_sledgehammer

imports Sledgehammer slam

begin

ML \<open>
  fun slam_tac { global_facts, local_facts } ctxt = 
    SELECT_GOAL (Slam_Tactic.slam_method ([], global_facts) ctxt local_facts)

  val slam_method = {
    name = "slam",
    string_of = "slam",
    is_proof_method_direct = true, 
    is_proof_method_multi_goal = false,
    needs_insert_local_facts = false,
    needs_insert_global_facts = false,
    tac = slam_tac,
    priority = 4
    (*
    try0_priority = 10,
    no_other_try0_methods = true
    *)
  }

  val r = Sledgehammer_Proof_Methods.register_dynamic_proof_method slam_method
\<close>

end
