theory hclause
                              
imports JEHA_TEST_BASE.test_base

begin

ML \<open>
  open HClause
  fun mk t = { th = Skip_Proof.make_thm @{theory} t, skolems = [] }
  fun eq_thm ({ th = th1, ... }: HClause.hthm, { th = th2, ...}: HClause.hthm) =
    Thm.eq_thm (th1, th2)
\<close>

declare [[show_types]]

ML_val \<open>
  val _ = Jeha_Proof.hclause_of_axiom @{context} @{thm mem_Collect_eq}
\<close>

ML_val \<open>
  val C = mk @{prop "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> False"}
  (* HClause.make_last *)
  val () = \<^assert> (eq_thm (make_last 0 C, mk @{prop "B \<Longrightarrow> C \<Longrightarrow> A \<Longrightarrow> False"}))
  val () = \<^assert> (eq_thm (make_last 1 C, mk @{prop "A \<Longrightarrow> C \<Longrightarrow> B \<Longrightarrow> False"}))
  val () = \<^assert> (eq_thm (make_last 2 C, C))
  val () = \<^assert_cant>\<open>HClause.make_last 3 C\<close>
  (* HClause.move_last_to *)
  val () = \<^assert> (eq_thm (move_last_to 0 C, mk @{prop "C \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow> False"}))
  val () = \<^assert> (eq_thm (move_last_to 1 C, mk @{prop "A \<Longrightarrow> C \<Longrightarrow> B \<Longrightarrow> False"}))
  val () = \<^assert> (eq_thm (move_last_to 2 C, C))
  val () = \<^assert_cant>\<open>HClause.move_last_to 3 C\<close>
  (* HClause.move_from_to *)
  val () = \<^assert> (eq_thm (move_from_to 0 0 C, C)) 
  val () = \<^assert> (eq_thm (move_from_to 0 1 C, mk @{prop "B \<Longrightarrow> A \<Longrightarrow> C \<Longrightarrow> False"}))
  val () = \<^assert> (eq_thm (move_from_to 0 2 C, mk @{prop "B \<Longrightarrow> C \<Longrightarrow> A \<Longrightarrow> False"}))
  val () = \<^assert> (eq_thm (move_from_to 1 0 C, mk @{prop "B \<Longrightarrow> A \<Longrightarrow> C \<Longrightarrow>  False"})) 
  val () = \<^assert> (eq_thm (move_from_to 1 1 C, C))
  val () = \<^assert> (eq_thm (move_from_to 1 2 C, mk @{prop "A \<Longrightarrow> C \<Longrightarrow> B \<Longrightarrow> False"}))
  val () = \<^assert> (eq_thm (move_from_to 2 0 C, mk @{prop "C \<Longrightarrow> A \<Longrightarrow> B \<Longrightarrow>  False"})) 
  val () = \<^assert> (eq_thm (move_from_to 2 1 C, mk @{prop "A \<Longrightarrow> C \<Longrightarrow> B \<Longrightarrow> False"}))
  val () = \<^assert> (eq_thm (move_from_to 2 2 C, C))
  (* HClause.negate_head *)
  val () = \<^assert> (eq_thm (negate_head @{context} C, mk @{prop "A \<Longrightarrow> B \<Longrightarrow> \<not>C"}))
  val () = \<^assert> (eq_thm (negate_head @{context} (mk @{prop "A \<Longrightarrow> False"}), mk @{prop "\<not>A"}))
  val () = \<^assert> (eq_thm (negate_head @{context} (mk @{prop "\<not>A \<Longrightarrow> False"}), mk @{prop "A"}))
  val () = \<^assert> (eq_thm (negate_head @{context} (mk @{prop "\<not>\<not>A \<Longrightarrow> False"}), mk @{prop "\<not>A"}))
  val () = \<^assert_cant>\<open>negate_head @{context} (mk @{prop "A"})\<close>
  val () = \<^assert_cant>\<open>negate_head @{context} (mk @{prop "A \<Longrightarrow> B"})\<close>
\<close>

ML_val \<open>
  val C = mk @{prop "A \<Longrightarrow> False"}
  (* HClause.make_last *)
  val () = \<^assert> (eq_thm (make_last 0 C, C)) 
  val () = \<^assert_cant>\<open>HClause.make_last 1 C\<close>
  (* HClause.move_last_to *)
  val () = \<^assert> (eq_thm (move_last_to 0 C, C))
  val () = \<^assert_cant>\<open>HClause.move_last_to 1 C\<close>
  (* HClause.move_from_to *)
  val () = \<^assert> (eq_thm (move_from_to 0 0 C, C)) 
  val () = \<^assert_cant>\<open>move_from_to 0 1 C\<close>
  val () = \<^assert_cant>\<open>move_from_to 1 0 C\<close>
\<close>

ML_val \<open>
  (* HClause.dest_lit_at *)
  val C = mk @{prop "s = t \<Longrightarrow> u \<noteq> v \<Longrightarrow> False"}
  val (s, t, false) = dest_lit_at 0 C
  val (u, v, true) = dest_lit_at 1 C
  val frees = map Free (fold_aterms Term.add_frees (Thm.prop_of (HClause.thm_of C)) [])
  val () = \<^assert> (eq_list (op aconv) (frees, [v, u, t, s]))
\<close>

end