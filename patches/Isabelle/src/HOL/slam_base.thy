theory slam_base
  imports Transfer Argo
begin

(* Simple wrapper around 'a itself (think: newtype) *)

datatype 'a type_arg_wrapper = Skolem_Type_Arg (inner: "'a itself")

term "Skolem_Type_Arg TYPE(bool)"

(* Used for pretty printing expression with a highlighted subterm. *)

definition slam_highlight :: "'a \<Rightarrow> 'a" where
  "slam_highlight subterm = subterm"

syntax
  "_slam_highlight" :: "'a \<Rightarrow> 'a" (\<open>\<langle><\<lblot>_\<rblot>>\<rangle>\<close>)

syntax_consts
  "_slam_highlight" \<rightleftharpoons> slam_highlight

translations
  "\<langle><\<lblot>t\<rblot>>\<rangle>" \<rightleftharpoons> "CONST slam_highlight t"

(* Used for pretty printing oriented literals. *)

definition slam_orient :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "slam_orient l r = (l = r)"

syntax slam_orient :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

syntax "_slam_orient" :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>\<langle><\<lblot>_ \<approx>~-> _\<rblot>>\<rangle>\<close>)

syntax_consts
  "_slam_orient" \<rightleftharpoons> slam_orient

translations
  "\<langle><\<lblot>l \<approx>~-> r\<rblot>>\<rangle>" \<rightleftharpoons> "CONST slam_orient l r"

ML_file \<open>Tools/Slam/slam_common.ML\<close>
ML_file \<open>Tools/Slam/slam_id.ML\<close>
ML_file \<open>Tools/Slam/jterm.ML\<close>
ML_file \<open>Tools/Slam/slam_symbol_table.ML\<close>
ML_file \<open>Tools/Slam/slam_order_reference.ML\<close>
ML_file \<open>Tools/Slam/slam_order.ML\<close>
ML_file \<open>Tools/Slam/slam_kbo.ML\<close>
ML_file \<open>Tools/Slam/jlit.ML\<close>
ML_file \<open>Tools/Slam/jclause_pos.ML\<close>
ML_file \<open>Tools/Slam/slam_log.ML\<close>
ML_file \<open>Tools/Slam/jclause.ML\<close>
ML_file \<open>Tools/Slam/slam_argo.ML\<close>
ML_file \<open>Tools/Slam/slam_index.ML\<close>
ML_file \<open>Tools/Slam/slam_fuel.ML\<close>
ML_file \<open>Tools/Slam/slam_isabelle_unify.ML\<close>
ML_file \<open>Tools/Slam/slam_isabelle_more_unify.ML\<close>
ML_file \<open>Tools/Slam/slam_unify.ML\<close>
ML_file \<open>Tools/Slam/slam_subsumption.ML\<close>
ML_file \<open>Tools/Slam/slam_simplify.ML\<close>
ML_file \<open>Tools/Slam/slam_passive.ML\<close>
ML_file \<open>Tools/Slam/slam_clause_set.ML\<close>
ML_file \<open>Tools/Slam/slam.ML\<close>

end
