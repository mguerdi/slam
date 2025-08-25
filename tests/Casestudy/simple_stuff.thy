theory simple_stuff

imports Main JEHA.jeha

begin

theorem T0: "\<exists>F. \<forall>T :: bool. \<exists>(S :: bool\<Rightarrow>bool). F S = T"
  using [[jeha_trace, (* jeha_trace_forward_simp=false,*) jeha_trace_clause_subsumption, jeha_max_number_of_steps=30]] by jeha
(*
zipperposition: One-line proof reconstruction failed: by metis

Isar proof (53 ms):
proof -
  { fix bb :: "((bool \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool"
    have "(\<exists>p pa. \<not> bb p \<and> \<not> p pa) \<or> (\<exists>p pa. bb p \<and> p pa) \<or> (\<exists>p pa. bb p \<and> p pa)"
      by blast }
  then show ?thesis
    by (metis (full_types))
qed 
zipperposition: One-line proof reconstruction failed: by metis 
zipperposition: Duplicate proof 
vampire: One-line proof reconstruction failed: by (metis inf_min inf_top.comm_monoid_axioms not_top_less) 
e: Try this: by (metis Ball_def Diff_cancel UNIV_I empty_iff mem_Collect_eq set_diff_eq top_set_def) (> 1.0 s, timed out) 
vampire: Try this: by (metis Rel_abs Rel_app Rel_def le_boolD le_boolI') (4.1 s) 
verit: Try this: by (metis (mono_tags, lifting) ASSUMPTION_D GreatestI2_order eq_id_iff inf_le1 le_boolD verit_comp_simplify1(2)) (978 ms) 
Done
*)

typedecl i
consts a::i b::i

axiomatization where
  A1: "\<not>(a = b)" and
  A2: "\<forall>x::i. x = a \<or> x = b"

(* There is a predicate F on bool\<Rightarrow>bool, whose image contains both True and False" *)
theorem T1: "\<exists>(F::(i\<Rightarrow>bool)\<Rightarrow>i). \<forall>T::i. (\<exists>(S::i\<Rightarrow>bool). F S = T)"
  (* nitpick[satisfy, user_axioms, show_all] *)
  (* by (metis A1 A2) *)
  (* (* using [[jeha_trace, *) using [[jeha_max_number_of_steps=1500]] by (jeha A1 A2) *)
  (* sledgehammer(A1 A2) *)
  (* using [[jeha_trace, jeha_max_number_of_steps=100]] by (jeha A1 A2) *)
  (* by metis *)
  using [[jeha_trace, jeha_max_number_of_steps=1500, jeha_trace_forward_simp=false, jeha_literal_selection_function="select_none", jeha_sup_variable_condition="none"]] by (jeha A1 A2)

end