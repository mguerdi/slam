theory jeha_base
  imports Transfer Argo
begin

(* Simple wrapper around 'a itself (think: newtype) *)

datatype 'a type_arg_wrapper = Skolem_Type_Arg (inner: "'a itself")

term "Skolem_Type_Arg TYPE(bool)"

ML_val \<open>
  val t = @{term "Skolem_Type_Arg"}
  val c = @{const Skolem_Type_Arg(bool)}
\<close>

(* Used for pretty printing expression with a highlighted subterm. *)

definition highlight :: "'a \<Rightarrow> 'a" where
  "highlight subterm = subterm"

syntax
  "_highlight" :: "'a \<Rightarrow> 'a" (\<open><_>\<close>)

syntax_consts
  "_highlight" \<rightleftharpoons> highlight

translations
  "<t>" \<rightleftharpoons> "CONST highlight t"

(* Used for pretty printing oriented literals. *)

definition orient :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "orient l r = (l = r)"

syntax orient :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

syntax "_orient" :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open><_ \<approx>> _>\<close>)

syntax_consts
  "_orient" \<rightleftharpoons> orient

translations
  "<l \<approx>> r>" \<rightleftharpoons> "CONST orient l r"

ML_file \<open>Tools/Jeha/jeha_common.ML\<close>
ML_file \<open>Tools/Jeha/jeha_id.ML\<close>
ML_file \<open>Tools/Jeha/jterm.ML\<close>
ML_file \<open>Tools/Jeha/jeha_symbol_table.ML\<close>
ML_file \<open>Tools/Jeha/jeha_order_reference.ML\<close>
ML_file \<open>Tools/Jeha/jeha_order.ML\<close>
ML_file \<open>Tools/Jeha/jeha_kbo.ML\<close>
ML_file \<open>Tools/Jeha/jlit.ML\<close>
ML_file \<open>Tools/Jeha/jclause_pos.ML\<close>
ML_file \<open>Tools/Jeha/jeha_log.ML\<close>
ML_file \<open>Tools/Jeha/jclause.ML\<close>
ML_file \<open>Tools/Jeha/jeha_argo.ML\<close>
ML_file \<open>Tools/Jeha/jeha_index.ML\<close>
ML_file \<open>Tools/Jeha/jeha_unify.ML\<close>
ML_file \<open>Tools/Jeha/jeha_subsumption.ML\<close>
ML_file \<open>Tools/Jeha/jeha_simplify.ML\<close>
ML_file \<open>Tools/Jeha/jeha_passive.ML\<close>
ML_file \<open>Tools/Jeha/jeha_clause_set.ML\<close>
ML_file \<open>Tools/Jeha/jeha.ML\<close>

end
