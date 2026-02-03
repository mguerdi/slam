theory slam_base
  imports HOL.Transfer HOL.Argo
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

ML\<open>
  (* compare ML_Pretty.make_string_fn *)
  val make_pretty_fn =
    "(fn x => Pretty.str (ML_Pretty.string_of (ML_system_pretty \
      \(x, FixedInt.fromInt (ML_Print_Depth.get_print_depth ())))))";

  val _ = Theory.setup
    (ML_Antiquotation.inline (Binding.make ("mk_pty", \<^here>)) (Args.context >> K make_pretty_fn))
\<close>

ML_file \<open>slam_common.ML\<close>
ML_file \<open>slam_id.ML\<close>
ML_file \<open>jterm.ML\<close>
ML_file \<open>slam_symbol_table.ML\<close>
ML_file \<open>slam_order_reference.ML\<close>
ML_file \<open>slam_order.ML\<close>
ML_file \<open>slam_kbo.ML\<close>
ML_file \<open>jlit.ML\<close>
ML_file \<open>slam_fuel.ML\<close>
ML_file \<open>slam_isabelle_unify.ML\<close>
ML_file \<open>slam_isabelle_more_unify.ML\<close>
ML_file \<open>slam_unify.ML\<close>
ML_file \<open>jclause_pos.ML\<close>
ML_file \<open>slam_log.ML\<close>
ML_file \<open>jclause.ML\<close>
ML_file \<open>slam_argo.ML\<close>
ML_file \<open>slam_index.ML\<close>
ML_file \<open>slam_subsumption.ML\<close>
ML_file \<open>slam_simplify.ML\<close>
ML_file \<open>slam_passive.ML\<close>
ML_file \<open>slam_clause_set.ML\<close>
ML_file \<open>slam.ML\<close>

end
