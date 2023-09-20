theory jeha_demo

imports Main HOL.Hilbert_Choice

begin

notation (output) "Pure.prop" ("#_" [1000] 1000)

(* Antiquotations for term and type patterns from the cookbook. *)
ML \<open>
  val term_pat_setup =
  let
    val parser = Args.context -- Scan.lift Parse.embedded_inner_syntax

    fun term_pat (ctxt, str) =
      str |> Proof_Context.read_term_pattern ctxt |> ML_Syntax.print_term |> ML_Syntax.atomic
  in
    ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat)
  end

  val type_pat_setup =
  let
    val parser = Args.context -- Scan.lift Parse.embedded_inner_syntax

    fun typ_pat (ctxt, str) =
      let
        val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
      in
        str |> Syntax.read_typ ctxt' |> ML_Syntax.print_typ |> ML_Syntax.atomic
      end
  in
    ML_Antiquotation.inline @{binding "typ_pat"} (parser >> typ_pat)
  end
\<close>

setup \<open> term_pat_setup \<close>

setup \<open> type_pat_setup \<close>

ML \<open>
  fun verbose_of ctxt = config_put_many_bool ctxt
    [show_types, show_brackets, show_markup, (* show_sorts, *) show_structs]
  and config_put_many_bool ctxt options =
    List.foldr (fn (option, ctxt) => Config.put option true ctxt) ctxt options
  fun pretty_term ctxt t = Syntax.pretty_term ctxt t |> Pretty.string_of
  fun pretty_terms ctxt terms =
    terms
    |> map (Syntax.pretty_term ctxt)
    |> Pretty.commas |> Pretty.block |> Pretty.string_of
  fun pretty_type ctxt typ = Pretty.string_of (Syntax.pretty_typ ctxt typ)
\<close>

ML \<open>
  local
    fun pp_pair (x, y) = Pretty.list "(" ")" [x, y]
    fun pp_triple (x, y, z) = Pretty.list "(" ")" [x, y, z]
    fun pp_list xs = Pretty.list "[" "]" xs
    fun pp_str s = Pretty.str s
    fun pp_qstr s = Pretty.quote (pp_str s)
    fun pp_int i = pp_str (string_of_int i)
    fun pp_sort S = pp_list (map pp_qstr S)
    fun pp_constr a args = Pretty.block [pp_str a, Pretty.brk 1, args]
  in
  fun raw_pp_typ (TVar ((a, i), S)) = pp_constr "TVar" (pp_pair (pp_pair (pp_qstr a, pp_int i), pp_sort S))
  | raw_pp_typ (TFree (a, S)) = pp_constr "TFree" (pp_pair (pp_qstr a, pp_sort S))
  | raw_pp_typ (Type (a, tys)) =  pp_constr "Type" (pp_pair (pp_qstr a, pp_list (map raw_pp_typ tys)))
  fun raw_pp_term  (Const (c, T)) = pp_constr "Const" (pp_pair (pp_qstr c, raw_pp_typ T))
    | raw_pp_term (Free (x, T)) = pp_constr "Free" (pp_pair (pp_qstr x, raw_pp_typ T))
    | raw_pp_term (Var ((x, i), T)) = pp_constr "Var" (pp_pair (pp_pair (pp_qstr x, pp_int i), raw_pp_typ T))
    | raw_pp_term (Bound i) = pp_constr "Bound" (pp_int i)
    | raw_pp_term (Abs(x, T, t)) = pp_constr "Abs" (pp_triple (pp_qstr x, raw_pp_typ T, raw_pp_term t))
    | raw_pp_term (s $ t) = pp_constr "$" (pp_pair (raw_pp_term s, raw_pp_term t))
  end;
  ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_pp_typ);
  ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_pp_term);
  val some_typ = @{typ "'a \<Rightarrow> 'b"}
  val _ = writeln (pretty_type @{context} some_typ)
  val list_typ = @{typ "'a list"}
  val _ = writeln (pretty_type @{context} some_typ)
  val bool_typ = @{typ "bool"}
  val int_typ = @{typ "int"}
  val _ = writeln (pretty_type @{context} (Type ("Int.int", [])));
  (* reset to default pretty printer *)
  ML_system_pp (fn depth => fn _ => ML_Pretty.to_polyml o Pretty.to_ML depth o Proof_Display.pp_typ Theory.get_pure);
  ML_system_pp (fn depth => fn _ => ML_Pretty.to_polyml o Pretty.to_ML depth o Proof_Display.pp_term Theory.get_pure);
\<close>

ML_file \<open>jeha_common.ML\<close>
ML_file \<open>clause_id.ML\<close>
ML_file \<open>jterm.ML\<close>
ML_file \<open>jeha_order_reference.ML\<close>
ML_file \<open>jeha_order.ML\<close>
ML_file \<open>jlit.ML\<close>
ML_file \<open>jclause_pos.ML\<close>
ML_file \<open>jeha_log.ML\<close>
ML_file \<open>jclause.ML\<close>
(* ML_file \<open>jeha_proof.ML\<close> *)
ML_file \<open>jeha_unify.ML\<close>
ML_file \<open>jeha_subsumption.ML\<close>
ML_file \<open>jeha.ML\<close>
ML_file \<open>jeha_tactic.ML\<close>

declare [[jeha_trace = true]]

ML \<open>
  val sb = Config.get @{context} Unify.search_bound
  val tb = Config.get @{context} Unify.trace_bound
\<close>

declare [[unify_search_bound = 10]]
declare [[unify_trace_bound = 10]]

ML \<open>
  val sb = Config.get @{context} Unify.search_bound
  val tb = Config.get @{context} Unify.trace_bound
\<close>

lemma paper_example_26:
  shows "(\<exists> y. \<forall> x . y x = (p x \<and> q x)) \<noteq> False"
  by (jeha)

(*

lemma "f = g \<Longrightarrow> (\<And> x. f x = (id o g) x)"
  by (jeha comp_apply id_apply)

lemma transitivity_test:
  shows "(x = y) \<Longrightarrow> (y = z) \<Longrightarrow> (x = z)"
  by jeha
(* apply(tactic \<open>my_print_tac @{context}\<close>) *)

lemma arg_cong_test:
  shows "g = f \<Longrightarrow> g a = f a"
  by jeha

lemma
  shows "(1 :: nat) + 1 = 2"
  by (jeha (dump) Num.nat_1_add_1)

*)
