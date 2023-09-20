theory "kbo"
imports
  HOL.Main
  SpecCheck.SpecCheck_Dynamic
begin

ML \<open>
open SpecCheck
open SpecCheck_Dynamic
structure Gen = SpecCheck_Generator
structure Prop = SpecCheck_Property
structure Show = SpecCheck_Show
structure Shrink = SpecCheck_Shrink
structure Random = SpecCheck_Random
\<close>


ML_file \<open>../jeha_common.ML\<close>
ML_file \<open>../jterm.ML\<close>
ML_file \<open>../clause_id.ML\<close>
ML_file \<open>../jeha_order_reference.ML\<close>
ML_file \<open>../jeha_order.ML\<close>
ML_file \<open>../jlit.ML\<close>
ML_file \<open>../jclause_pos.ML\<close>
ML_file \<open>../jeha_log.ML\<close>
ML_file \<open>../jclause.ML\<close>
ML_file \<open>../jeha_index.ML\<close>

declare [[speccheck_max_success = 100]]
declare [[speccheck_num_counterexamples = 30]]
declare [[ML_print_depth = 100]]

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
  val fps = [[], [1]]
  val terms =
    [ @{term_pat "?x :: int"}
    , @{term_pat "c :: int"}
    , @{term_pat "d :: int"}
    , @{term_pat "f(d) :: int"}
    , @{term_pat "f(?x) :: int"}
    , @{term "\<lambda> x . d"}
    ]
  val keys = map (Term_Index.compute_key fps) terms
  val index = fold (Term_Index.insert_term fps) terms Term_Index.empty
  (* val _ =
    Term_Index.fold
      (K true)
      [Jeha_Index.FOFree "f", Jeha_Index.AnonymousVar]
      (fn t => K (writeln (Jeha_Common.pretty_term @{context} t)))
      index
      () *)
\<close>

declare [[speccheck_max_success = 100]]
declare [[speccheck_num_counterexamples = 30]]
declare [[show_types = true]]

ML \<open>
  fun term_num_args_gen nv ni weights num_args_gen h i =
    Gen.zip (Gen.aterm' (Gen.nonneg nv) (Gen.nonneg ni) weights) (num_args_gen h i)

  fun term_gen ctxt nv ni weights num_args_gen =
    let val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    in
      Gen.term_tree (term_num_args_gen nv ni weights num_args_gen)
      |> Gen.map (try (singleton (Variable.polymorphic ctxt') o Syntax.check_term ctxt'))
      |> Gen.filter is_some
      |> Gen.map the
    end

  fun term_pair_gen ctxt nv ni weights num_args_gen =
    let
      val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
      val term_gen = Gen.term_tree (term_num_args_gen nv ni weights num_args_gen)
    in
      Gen.zip term_gen term_gen
      |> Gen.map (fn (s, t) => try (Variable.polymorphic ctxt' o Syntax.check_terms ctxt') [s, t])
      |> Gen.filter is_some
      |> Gen.map (fn SOME [s, t] => (s, t))
    end

  fun num_args_gen max_h max_args h _ = if h > max_h then Gen.return 0 else Gen.nonneg max_args

  fun term_gen' ctxt nv ni weights max_h max_args =
    term_gen ctxt nv ni weights (num_args_gen max_h max_args)
  
  fun term_pair_gen' ctxt nv ni weights max_h max_args =
    term_pair_gen ctxt nv ni weights (num_args_gen max_h max_args)

  (* *)
  val term_gen_set = term_gen' @{context} 2 2 (1, 1, 1, 0) 4 4

  (* (weight_const, weight_free, weight_var, weight_bound) *)
  (* these weights achieve ~50 percent unifiability *)
  val term_pair_gen_set = term_pair_gen' @{context} 2 2 (4,4,1,0) 4 4

  val check_term = check (Show.term @{context}) term_gen_set

  fun show_termpair ctxt =
    let val pretty_term = Syntax.pretty_term ctxt
    in SpecCheck_Show.zip pretty_term pretty_term end

  val check_term_pair = check (show_termpair @{context}) term_pair_gen_set

  fun unify_retrieve (s, t) =
    let
      val fps = [[]]
      val index = Term_Index.insert_term fps s Term_Index.empty
    in
      (((if is_some (Seq.pull (Unify.unifiers (Context.Proof @{context}, Envir.init, [(s, t)])))
        then (
          if 0 = length (Term_Index.get_unifiables fps t index)
            then (false; error "bad")
            else (writeln ("GOOD (|s|, |t|) = (" ^ @{make_string} (size_of_term s) ^ ", " ^ @{make_string} (size_of_term t) ^ ")"); true)
          )
        else (writeln "VACUOUS"; true))
      handle ListPair.UnequalLengths => (writeln "CAUGHT"; true))
      handle TERM msg => (writeln ("TERM: " ^ fst msg ^ " (s,t) = " ^ Jeha_Common.pretty_terms @{context} [s,t]); true))
      handle TYPE _ => (writeln "TYPE"; true)
    end

  val _ = Lecker.test_group @{context} (Random.new ()) [
    (* Prop.prop (fn t => false) |> check_term "no loose bvars" *)
    (* Prop.prop (K false) |> check_term_pair "some term pairs" *)
    Prop.prop (unify_retrieve) |> check_term_pair "unifiables retrieved"
  ]
\<close>

declare [[speccheck_num_counterexamples = 30]]

ML \<open>
  val ctxt = Context.Proof @{context}
\<close>

ML \<open>
  fun type_checks t = (type_of t; false) handle _ => true
\<close>

ML_command \<open>
  check_dynamic @{context} "ALL s t. not (type_checks s) orelse not (type_checks t) orelse is_some (Unify.matcher ctxt [s] [t])"
\<close>

declare [[speccheck_max_success = 10000000]]
ML_command \<open>
check_dynamic @{context} "ALL s t. type_checks t orelse type_checks s orelse (Jeha_Order.kbo_fast (s, t) = Jeha_Order_Reference.kbo (s, t))"
\<close>

declare [[speccheck_max_success = 10]]
ML_command \<open>
check_dynamic @{context} "ALL s t. (Jeha_Order.kbo_fast (s, t) = Jeha_Order_Reference.kbo (s, t))"
\<close>

(*
(??.c_8 ??.c_8, ??.c_8 ?v_8.0 ?v_8.1) 
    ?c    ?c  ,   ?c     ?v     ?w
*)

declare [[speccheck_max_success = 10]]
declare [[speccheck_num_counterexamples = 30]]
declare [[ML_print_depth = 100]]

ML \<open>
  (* \<forall> \<iota> (\<lambda>x. p y y (\<lambda>u. f y y (\<forall> \<iota> (\<lambda>v. u)))) *)
  val example_term = @{term_pat "\<forall> x. p ?y ?y (\<lambda> u. f ?y ?y (\<forall> v. ?u))"}
  val translated = Jeha_Order_Reference.to_fo_term example_term
  (* val _ = writeln (Jeha_Order_Reference.pretty_fo_term @{context} translated) *)
  val ground_lambda = @{term "\<lambda>x. x"}
  val might_be_fluid = JTerm.might_be_fluid ground_lambda
  val ground_translated = Jeha_Order_Reference.to_fo_term ground_lambda
  (* val _ = writeln (Jeha_Order_Reference.pretty_fo_term @{context} ground_translated) *)
  val with_green_subterms = @{term_pat "(f :: 'a => 'b => 'c) ?x ((g :: 'd => 'e => 'b) ?y b)"}
  val green_subterm_1 = @{term_pat "?x :: 'a"}
  val green_subterm_2 = @{term_pat "(g :: 'd \<Rightarrow> 'e \<Rightarrow> 'b) ?y b"}
  val green_subterm_3 = @{term_pat "b :: 'e"}
  val with_green_subterms_translated = Jeha_Order_Reference.to_fo_term with_green_subterms
  val _ = writeln ("with_green_subterms_translated:  " ^ Jeha_Order_Reference.pretty_fo_term @{context} with_green_subterms_translated)
  val green_subterm_1_translated = Jeha_Order_Reference.to_fo_term green_subterm_1
  val green_subterm_2_translated = Jeha_Order_Reference.to_fo_term green_subterm_2
  val _ = writeln ("green_subterm_2: " ^ Jeha_Order_Reference.pretty_fo_term @{context} green_subterm_2_translated)
  val green_subterm_3_translated = Jeha_Order_Reference.to_fo_term green_subterm_3
  val _ = writeln ("green_subterm_3: " ^ Jeha_Order_Reference.pretty_fo_term @{context} green_subterm_3_translated)
  val ge_1 = Jeha_Order_Reference.fo_kbo_greater (with_green_subterms_translated, green_subterm_1_translated)
  val ge_2 = Jeha_Order_Reference.fo_kbo_greater (with_green_subterms_translated, green_subterm_2_translated)
  val ge_3 = Jeha_Order_Reference.fo_kbo_greater (with_green_subterms_translated, green_subterm_3_translated)
  (* g ?y b > b *)
  val ge_23 = Jeha_Order_Reference.fo_kbo_greater (green_subterm_2_translated, green_subterm_3_translated)
  val kbo_gyb_b = Jeha_Order_Reference.kbo (green_subterm_2, green_subterm_3)
\<close>

ML \<open>
fun close_term t =
  let val largest_loose_bvar = fold (curry Int.max) (loose_bnos t) ~1 in
    fold (fn _ => fn u => Abs ("", dummyT, u)) (0 upto largest_loose_bvar) t
  end

fun my_aterm' num_variants_gen index_gen nb weights =
  let val weights = if nb < 0 then (#1 weights, #2 weights, #3 weights, 0) else weights in
    Gen.aterm (Gen.const' num_variants_gen) (Gen.free' num_variants_gen) (Gen.var' num_variants_gen index_gen)
      (Gen.bound (Gen.nonneg nb)) weights
  end

fun term_num_args_gen ctxt' nv ni nb weights num_args_gen h i =
  Gen.zip
    ( Gen.one_ofWL
        [ (9, my_aterm' (Gen.nonneg nv) (Gen.nonneg ni) nb weights)
        , (1, Gen.map (fn u => Abs ("", dummyT, u)) (fn r => term_gen ctxt' (if nv > 0 then nv - 1 else 0) (if ni > 0 then ni - 1 else 0) (nb + 1) weights num_args_gen r))
        ]
    )
    (num_args_gen h i)
and term_gen ctxt nv ni nb weights num_args_gen =
  let val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
  in
    Gen.term_tree (term_num_args_gen ctxt' nv ni nb weights num_args_gen)
    |> Gen.map (try (singleton (Variable.polymorphic ctxt') o (* Syntax.check_term ctxt' o *) close_term))
    |> Gen.filter is_some
    |> Gen.map the
  end

fun num_args_gen max_h max_args h _ = if h > max_h then Gen.return 0 else Gen.nonneg max_args

fun term_gen' ctxt nv ni nb weights max_h max_args =
  term_gen ctxt nv ni nb weights (num_args_gen max_h max_args)

val typ_gen =
  Gen.typ''
    (Gen.nonneg 8) (* num_variants_gen *)
    (Gen.nonneg 4) (* arity_gen *)
    (Gen.nonneg 4) (* tfree_gen *)
    (1, 1, 1) (* (wtype, wtfree, wtvar) *)

val logical_types = Type.logical_types (Sign.tsig_of @{theory})
(* val type_space = Type.type_space (Sign.tsig_of @{theory}) *)
val types = (Name_Space.dest_table o #types o Type.rep_tsig o Sign.tsig_of) @{theory}
val _ = map (writeln o @{make_string}) types
(* val type_names = Name_Space.get_names type_space *)
(* val _ = writeln (@{make_string} type_names) *)
(* val arities = map_filter (try (fn tname => (tname, Type.arity_number (Sign.tsig_of @{theory}) tname))) type_names *)
val consts = Sign.consts_of @{theory}
val constants = (#constants (Consts.dest consts))
val constraints = (#constraints (Consts.dest consts))
\<close>

ML_command \<open>
let
  val int_gen = Gen.range_int (~10000000, 10000000)
  val size_gen = Gen.nonneg 10
  (* check : 'a SpecCheck_Show.show -> ('a, 's) SpecCheck_Generator.gen_state -> string ->
       'a SpecCheck_Property.prop -> (Proof.context, 's) Lecker.test_state *)
  val check_term = check (Show.term @{context}) (term_gen' @{context} 2 2 0 (0, 1, 1, 1) 2 2)
  val check_typ = check (Show.typ @{context}) typ_gen
  (* val check_list = check_shrink (Show.list Show.int) (Shrink.list Shrink.int)
    (Gen.list size_gen int_gen) *)
  fun list_test (k, f, xs) =
    AList.lookup (op=) (AList.map_entry (op=) k f xs) k = Option.map f (AList.lookup (op=) xs k)

  val list_test_show = Show.zip3 Show.int Show.none (Show.list (Show.zip Show.int Show.int))
  val list_test_gen = Gen.zip3 int_gen (Gen.function' int_gen)
    (Gen.list size_gen (Gen.zip int_gen int_gen))
in
  Lecker.test_group @{context} (Random.new ()) [
    (* Prop.prop (fn t => false) |> check_term "no loose bvars" *)
    Prop.prop (fn T => false) |> check_typ "some types"
    (* Prop.prop (fn xs => rev xs = xs) |> check_list "rev = I",
    Prop.prop (fn xs => rev (rev xs) = xs) |> check_list "rev o rev = I",
    Prop.prop list_test |> check list_test_show list_test_gen "lookup map equiv map lookup" *)
  ]
end
\<close>

ML_command \<open>
check_dynamic @{context} "ALL t. loose_bvar (t, 0)"
\<close>

(* strictness of kbo *)
ML_command \<open>
check_dynamic @{context} "ALL s t. Jeha_Common.map_some rev_order (Jeha_Order.kbo_fast (t, s)) = Jeha_Order.kbo_fast (s, t)"
\<close>

ML_command \<open>
check_dynamic @{context} "ALL s t. (SOME EQUAL = Jeha_Order.kbo_fast (s, t)) = (s aconv t)"
\<close>

(* literals *)
ML \<open>
  datatype 'a with_bot = Bot | It of 'a
  fun bot_ord _ (Bot, Bot) = SOME EQUAL
    | bot_ord _ (Bot, _) = SOME LESS
    | bot_ord _ (_, Bot) = SOME GREATER
    | bot_ord cmp (It s, It t) = cmp (s, t)
  fun bot_eq cmp (x, y) = (SOME EQUAL) = bot_ord ((fn b => if b then SOME EQUAL else NONE) o cmp) (x, y)
  fun ms_of_lit (s, t, true) = [[It s], [It t]]
    | ms_of_lit (s, t, false) = [[It s, Bot], [It t, Bot]]
  val ms_lit_eq = apply2 ms_of_lit #> (Jeha_Order.multiset_eq (Jeha_Order.multiset_eq (bot_eq (op aconv))))
  val ms_lit_g =
    apply2 ms_of_lit
    #>
    Jeha_Order.multiset_is_greater_reference
      (Jeha_Order.multiset_is_greater_reference
        (bot_ord Jeha_Order.kbo_fast #> curry op= (SOME GREATER))
        (bot_eq (op aconv)))
      (Jeha_Order.multiset_eq (bot_eq (op aconv)))
  fun are_equal_lit_ords (l, r) =
    case JLit.kbo (l, r) of
      SOME LESS => ms_lit_g (r, l)
    | SOME GREATER => ms_lit_g (l, r)
    | SOME EQUAL => ms_lit_eq (l, r)
    | NONE => true (* FIXME *)
\<close>

ML \<open>
  val ms_lit_generic_eq = apply2 ms_of_lit #> (Jeha_Order.multiset_eq (Jeha_Order.multiset_eq (bot_eq op=)))
  fun ms_lit_generic_g cmp =
    apply2 ms_of_lit
    #>
    Jeha_Order.multiset_is_greater_reference
      (Jeha_Order.multiset_is_greater_reference
        (bot_ord cmp #> curry op= (SOME GREATER))
        (bot_eq op=))
      (Jeha_Order.multiset_eq (bot_eq op=))
  fun are_equal_lit_generic_ords cmp (l, r) =
    case JLit.kbo_generic cmp (l, r) of
      SOME LESS => ms_lit_generic_g cmp (r, l)
    | SOME GREATER => ms_lit_generic_g cmp (l, r)
    | SOME EQUAL => ms_lit_generic_eq (l, r)
    | NONE => true (* FIXME *)
  val are_equal_lit_int_ords = are_equal_lit_generic_ords (SOME o int_ord)
\<close>

declare [[speccheck_max_success = 1000000]]
ML_command \<open>
  val small_int_gen = Gen.range_int (~100, 100)
  val lit_int_gen =
    Gen.zip small_int_gen small_int_gen
    |> Gen.zip (Gen.bernoulli 0.5)
    |> Gen.map (fn (b, (s, t)) => (s, t, b))
  val show_lit_int = @{make_string} #> Pretty.str
  val check_lit_int_pair = check (Show.zip show_lit_int show_lit_int) (Gen.zip lit_int_gen lit_int_gen)
  val lit_test = Lecker.test_group @{context} (Random.new ()) [
    Prop.prop (are_equal_lit_int_ords) |> check_lit_int_pair "some lits"
  ]
\<close>

declare [[speccheck_max_success = 100000]]
ML \<open>
  fun term_num_args_gen nv ni weights num_args_gen h i =
    Gen.zip (Gen.aterm' (Gen.nonneg nv) (Gen.nonneg ni) weights) (num_args_gen h i)
  fun term_gen ctxt nv ni weights num_args_gen =
    let val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    in
      Gen.term_tree (term_num_args_gen nv ni weights num_args_gen)
      |> Gen.map (try (singleton (Variable.polymorphic ctxt') o Syntax.check_term ctxt'))
      |> Gen.filter is_some
      |> Gen.map the
    end
  fun term_gen' ctxt nv ni weights max_h max_args =
    term_gen ctxt nv ni weights (num_args_gen max_h max_args)
  val term_gen_set = term_gen' @{context} 2 2 (1, 1, 1, 0) 4 4
  val tpair_gen = Gen.zip term_gen_set term_gen_set
  val eq_gen = Gen.map HOLogic.mk_eq tpair_gen
  val lit_gen =
    eq_gen
    |> Gen.zip (Gen.bernoulli 0.5)
    |> Gen.map (fn (b, t) => (if b then I else HOLogic.mk_not) t)
    |> Gen.map JLit.of_term
  (* val show_lit = JLit.pretty_lit' @{context} *)
  val show_lit = @{make_string} #> Pretty.str
  val check_lit = check show_lit lit_gen
  val check_lit_pair = check (Show.zip show_lit show_lit) (Gen.zip lit_gen lit_gen)
  val lit_test = Lecker.test_group @{context} (Random.new ()) [
    Prop.prop (are_equal_lit_ords) |> check_lit_pair "some lits"
  ]
\<close>

ML \<open>
  val bad_lits =
    apply2
      JLit.of_term
      (@{term_pat "(a :: ?'a) = a"}, @{term_pat "(b :: ?'a) = ?c"})
  val mss = apply2 ms_of_lit bad_lits
  val b = ms_lit_g bad_lits
  val b' = ms_lit_g (swap bad_lits)
  val b'' = JLit.kbo bad_lits
\<close>

declare [[speccheck_max_success = 10]]
(* multiset order *)

ML \<open>
  val int_list_eq = Jeha_Order.multiset_eq op=
  val int_list_list_eq = Jeha_Order.multiset_eq int_list_eq
  val int_list_g = Jeha_Order.multiset_is_greater_reference op> op=
  val int_list_list_g = Jeha_Order.multiset_is_greater_reference int_list_g int_list_eq
  val int_list_ord = Jeha_Order.mk_multiset_order_of_strict (SOME o int_ord)
  val int_list_list_ord = Jeha_Order.mk_multiset_order_of_strict int_list_ord 
  fun are_equal (l, r) =
    case int_list_list_ord (l, r) of
      SOME LESS => int_list_list_g (r, l)
    | SOME GREATER => int_list_list_g (l, r)
    | SOME EQUAL => int_list_list_eq (l, r)
    | NONE => (writeln "should be total"; false)
  val failure = ([[]], [])
  val b = int_list_list_g failure
  val b' = int_list_list_ord failure
  (* val non_total = ([[], [], [2124004389]], [[1798102523], [], []]) *)
  val non_total = ([[], [2]], [[], [1]])
  val bad = int_list_list_ord non_total
  val also_bad = int_list_list_ord (swap non_total)
  val g = int_list_list_g non_total
  val g' = int_list_list_g (swap non_total)
  val empty_less = int_list_ord ([], [1])
  val empty_less' = int_list_ord ([1], [])
  val int_list_g_not_total = ([3, 2], [10])
  val dzz = int_list_g int_list_g_not_total
  val dzz' = int_list_g (swap int_list_g_not_total)
  fun sub x y = fold (remove1 op=) y x
  val fa = forall (fn x => exists (fn y => op> (y, x)) [10]) [2, 3]
\<close>

ML \<open>
  val empty_vs_single = int_list_ord ([], [1])
  val single_vs_empty = int_list_ord ([1], [])
\<close>

(* BAD: *)
declare [[speccheck_max_success = 100000]]
ML_command \<open>
check_dynamic @{context} "ALL l r. NONE <> int_list_list_ord (l, r)"
\<close>

declare [[speccheck_max_success = 10000]]
ML_command \<open>
check_dynamic @{context} "ALL l r. (int_list_g (l, r) = not (int_list_g (r, l))) orelse int_list_eq (l, r)"
\<close>

declare [[speccheck_max_success = 10000]]
ML_command \<open>
check_dynamic @{context} "ALL l r. (int_list_list_g (l, r) = not (int_list_list_g (r, l))) orelse int_list_list_eq (l, r)"
\<close>

declare [[speccheck_max_success = 1000000]]
ML_command \<open>
check_dynamic @{context} "ALL l r. NONE <> int_list_ord (l, r)"
\<close>

(* ML_command \<open>
check_dynamic @{context} "ALL l r. (int_list ord 
\<close> *)

declare [[speccheck_max_success = 10]]
ML_command \<open>
check_dynamic @{context} "ALL l r. are_equal (l, r)"
\<close>

ML \<open>
fun set_partial_ord pair =
  let
    val (X, Y) = apply2 (sort_distinct int_ord) pair
  in
    case (subset (op =) (X, Y), subset (op =) (Y, X)) of
      (true, true) => SOME EQUAL
    | (true, false) => SOME LESS
    | (false, true) => SOME GREATER
    | (false, false) => NONE
  end
\<close>

ML_command \<open>
check_dynamic @{context} "ALL xs. forall (fn max => forall (fn x => SOME LESS <> set_partial_ord (max, x)) xs) (map_filter (fn (i, strict) => if strict then SOME (nth xs i) else NONE) (Jeha_Order.idxs_of_maximal_elements (set_partial_ord) xs))"
\<close>

ML_command \<open>
check_dynamic @{context} "ALL xs. forall (fn max => forall (fn x => max >= x) xs) (map (fn (i, _) => nth xs i) (Jeha_Order.idxs_of_maximal_elements (SOME o int_ord) xs))"
\<close>

subsection \<open>Unit Tests and Exceptions\<close>

ML \<open>
  fun faulty_abs n =
    if n < ~10000 then error "out of bounds"
    else if n < 0 then ~n
    else n
\<close>

ML_command \<open>
let
  val check_unit_int_pair = check_unit_tests (Show.zip Show.int Show.int)
  fun correctness_tests ctxt s = Lecker.test_group ctxt s [
      check_unit_int_pair  [(~10, 10), (0, 0), (10, 10)] "correctness small values"
        (Prop.prop (fn (n, exp) => faulty_abs n = exp)),
      check_unit_int_pair [(~999999999, 999999999), (999999999, 999999999)]
        "correctness large values" (Prop.prop (fn (n, exp) => faulty_abs n = exp))
    ]
  fun exception_tests ctxt s =
    let val exn_prop = Prop.expect_failure (ERROR "out of bounds") faulty_abs
    in
      Lecker.test_group ctxt s [
        check_unit_tests Show.int [~10, 0, 10] "expect exception for small values" exn_prop,
        check_unit_tests Show.int [~999999999, ~99999999999999] "expect exception for large values"
          exn_prop
      ]
    end
in
  Lecker.test_group @{context} () [
    check_unit_tests Show.int [~10, 0, 10] "is idempotent"
      (Prop.prop (fn n => faulty_abs (faulty_abs n) = faulty_abs n)),
    correctness_tests,
    exception_tests
  ]
end
\<close>

subsection \<open>Randomised Tests\<close>

ML_command \<open>
let
  val int_gen = Gen.range_int (~10000000, 10000000)
  val size_gen = Gen.nonneg 10
  val check_list = check_shrink (Show.list Show.int) (Shrink.list Shrink.int)
    (Gen.list size_gen int_gen)
  fun list_test (k, f, xs) =
    AList.lookup (op=) (AList.map_entry (op=) k f xs) k = Option.map f (AList.lookup (op=) xs k)

  val list_test_show = Show.zip3 Show.int Show.none (Show.list (Show.zip Show.int Show.int))
  val list_test_gen = Gen.zip3 int_gen (Gen.function' int_gen)
    (Gen.list size_gen (Gen.zip int_gen int_gen))
in
  Lecker.test_group @{context} (Random.new ()) [
    Prop.prop (fn xs => rev xs = xs) |> check_list "rev = I",
    Prop.prop (fn xs => rev (rev xs) = xs) |> check_list "rev o rev = I",
    Prop.prop list_test |> check list_test_show list_test_gen "lookup map equiv map lookup"
  ]
end
\<close>

text \<open>The next three examples roughly correspond to the above test group (except that there's no
shrinking). Compared to the string-based method, the method above is more flexible - you can change
your generators, shrinking methods, and show instances - and robust - you are not reflecting strings
(which might contain typos) but entering type-checked code. In exchange, it is a bit more work to
set up the generators. However, in practice, one shouldn't rely on default generators in most cases
anyway.\<close>

ML_command \<open>
check_dynamic @{context} "ALL xs. rev xs = xs";
\<close>

ML_command \<open>
check_dynamic @{context} "ALL xs. rev (rev xs) = xs";
\<close>

subsection \<open>AList Specification\<close>

ML_command \<open>
(*map_entry applies the function to the element*)
check_dynamic @{context} (implode
  ["ALL k f xs. AList.lookup (op =) (AList.map_entry (op =) k f xs) k = ",
   "Option.map f (AList.lookup (op =) xs k)"])
\<close>

ML_command \<open>
(*update always results in an entry*)
check_dynamic @{context} "ALL k v xs. AList.defined (op =) (AList.update (op =) (k, v) xs) k";
\<close>

ML_command \<open>
(*update always writes the value*)
check_dynamic @{context}
  "ALL k v xs. AList.lookup (op =) (AList.update (op =) (k, v) xs) k = SOME v";
\<close>

ML_command \<open>
(*default always results in an entry*)
check_dynamic @{context} "ALL k v xs. AList.defined (op =) (AList.default (op =) (k, v) xs) k";
\<close>

ML_command \<open>
(*delete always removes the entry*)
check_dynamic @{context} "ALL k xs. not (AList.defined (op =) (AList.delete (op =) k xs) k)";
\<close>

ML_command \<open>
(*default writes the entry iff it didn't exist*)
check_dynamic @{context} (implode
  ["ALL k v xs. (AList.lookup (op =) (AList.default (op =) (k, v) xs) k = ",
   "(if AList.defined (op =) xs k then AList.lookup (op =) xs k else SOME v))"])
\<close>

subsection \<open>Examples on Types and Terms\<close>


ML_command \<open>
check_dynamic @{context} "ALL f g t. map_types (g o f) t = (map_types f o map_types g) t";
\<close>

ML_command \<open>
check_dynamic @{context} "ALL f g t. map_types (f o g) t = (map_types f o map_types g) t";
\<close>


text \<open>One would think this holds:\<close>

ML_command \<open>
check_dynamic @{context} "ALL t ts. strip_comb (list_comb (t, ts)) = (t, ts)"
\<close>

text \<open>But it only holds with this precondition:\<close>

ML_command \<open>
check_dynamic @{context}
  "ALL t ts. case t of _ $ _ => true | _ => strip_comb (list_comb (t, ts)) = (t, ts)"
\<close>

subsection \<open>Some surprises\<close>

ML_command \<open>
check_dynamic @{context} "ALL Ts t. type_of1 (Ts, t) = fastype_of1 (Ts, t)"
\<close>


ML_command \<open>
val thy = \<^theory>;
check_dynamic (Context.the_local_context ())
  "ALL t u. if Pattern.matches thy (t, u) then Term.could_unify (t, u) else true"
\<close>

end
