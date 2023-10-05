theory "kbo"
imports
  test_base
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

declare [[speccheck_max_success = 100]]
declare [[speccheck_num_counterexamples = 30]]
declare [[ML_print_depth = 100]]

(* Antiquotations for term and type patterns from the cookbook. *)
setup \<open> Jeha_Common.term_pat_setup \<close>

setup \<open> Jeha_Common.type_pat_setup \<close>

setup \<open> Jeha_Common.term_schem_setup \<close>

declare [[speccheck_max_success = 100]]
declare [[speccheck_num_counterexamples = 30]]
declare [[show_types = true]]


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

declare [[speccheck_max_success = 10000]]
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

(* (O3) *) 
ML_val \<open>
  val ft = (@{term "False"}, @{term "True"});
  val fo_ft = apply2 Jeha_Order_Reference.to_fo_term ft;
  writeln (Jeha_Order_Reference.pretty_fo_term @{context} (#1 fo_ft));
  writeln (Jeha_Order_Reference.pretty_fo_term @{context} (#2 fo_ft));
  val t_g_f = Jeha_Order_Reference.fo_kbo_greater fo_ft;
  val f_g_t = Jeha_Order_Reference.fo_kbo_greater (swap fo_ft); 
  val false_kbo_true = Jeha_Order_Reference.kbo ft;
  \<^assert> (SOME GREATER = false_kbo_true);
  \<^assert> (SOME GREATER = Jeha_Order_Reference.kbo (@{term "a"}, @{term "False"}));
\<close>

ML_val \<open>
  (* Reference KBO: eq and greater: Abs ("x", "'a", Abs ("y", "'a", Const ("HOL.eq", "'a \<Rightarrow> 'a \<Rightarrow> bool") $ Bound 0 $ Bound 1)) and Abs ("x", "'a", Abs ("y", "'a", Const ("HOL.eq", "'a \<Rightarrow> 'a \<Rightarrow> bool") $ Bound 0 $ Bound 1)) *)
  val Ta = @{typ "'a"}
  val t = Abs ("x", Ta, Abs ("y", Ta, Const ("HOL.eq", @{typ "'a \<Rightarrow> 'a \<Rightarrow> bool"}) $ Bound 0 $ Bound 1));
  val s = @{term "\<lambda>x::'a. \<lambda>y::'a. y = x"};
  \<^assert> (s = t);
  val fo_t = Jeha_Order_Reference.to_fo_term t;
  writeln (Jeha_Order_Reference.pretty_fo_term @{context} fo_t);
  val u = @{term "\<lambda>x::'a. x"};
  val fo_u = Jeha_Order_Reference.to_fo_term u;
  val u_g_u = Jeha_Order_Reference.fo_kbo_greater (fo_u, fo_u);
  val u_refl = Jeha_Order.kbo (u, u)
\<close>

(* First order translation *)
ML_val \<open>
  (* \<forall> \<iota> (\<lambda>x. p y y (\<lambda>u. f y y (\<forall> \<iota> (\<lambda>v. u)))) *)
  val example_term = @{term_pat "\<forall> x. p ?y ?y (\<lambda> u. f ?y ?y (\<forall> v. ?u))"};
  val translated = Jeha_Order_Reference.to_fo_term example_term;
  (* val _ = writeln (Jeha_Order_Reference.pretty_fo_term @{context} translated) *)
  val ground_lambda = @{term "\<lambda>x. x"};
  val might_be_fluid = JTerm.might_be_fluid ground_lambda;
  \<^assert> (not might_be_fluid);
  val ground_translated = Jeha_Order_Reference.to_fo_term ground_lambda;
  (* val _ = writeln (Jeha_Order_Reference.pretty_fo_term @{context} ground_translated) *)
\<close>

(* Green subterm property, (O2) in o\<lambda>Sup paper *)
ML_val \<open>
  val term = @{term_schem "(f :: 'a => 'b => 'c) ?x ((g :: 'd => 'e => 'b) ?y b)"};
  val green_subterm_1 = @{term_schem "?x :: 'a"};
  val green_subterm_2 = @{term_schem "(g :: 'd \<Rightarrow> 'e \<Rightarrow> 'b) ?y b"};
  val green_subterm_3 = @{term_schem "b :: 'e"};
  val term_translated = Jeha_Order_Reference.to_fo_term term;
  val _ = writeln ("term_translated:  " ^ Jeha_Order_Reference.pretty_fo_term @{context} term_translated);
  val green_subterm_1_translated = Jeha_Order_Reference.to_fo_term green_subterm_1;
  val green_subterm_2_translated = Jeha_Order_Reference.to_fo_term green_subterm_2;
  val _ = writeln ("green_subterm_2: " ^ Jeha_Order_Reference.pretty_fo_term @{context} green_subterm_2_translated);
  val green_subterm_3_translated = Jeha_Order_Reference.to_fo_term green_subterm_3;
  val _ = writeln ("green_subterm_3: " ^ Jeha_Order_Reference.pretty_fo_term @{context} green_subterm_3_translated);
  fun kbo_greater s t = Jeha_Order_Reference.fo_kbo_greater (s, t); 
  \<^assert> (kbo_greater term_translated green_subterm_1_translated);
  \<^assert> (kbo_greater term_translated green_subterm_2_translated);
  \<^assert> (kbo_greater term_translated green_subterm_3_translated);
  (* g ?y b > b *);
  \<^assert> (kbo_greater green_subterm_2_translated green_subterm_3_translated);
  val kbo_gyb_b = Jeha_Order_Reference.kbo (green_subterm_2, green_subterm_3);
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
  (* extra element Bot which is the smallest *)
  datatype 'a with_bot = Bot | It of 'a
  fun bot_ord _ (Bot, Bot) = SOME EQUAL
    | bot_ord _ (Bot, _) = SOME LESS
    | bot_ord _ (_, Bot) = SOME GREATER
    | bot_ord cmp (It s, It t) = cmp (s, t)
  fun bot_eq cmp (x, y) = (SOME EQUAL) = bot_ord ((fn b => if b then SOME EQUAL else NONE) o cmp) (x, y)
  (* "the standard way" *)
  fun ms_of_lit (s, t, true) = [[It s], [It t]]
    | ms_of_lit (s, t, false) = [[It s, Bot], [It t, Bot]]
  val ms_lit_eq = apply2 ms_of_lit #> (Jeha_Order.multiset_eq (Jeha_Order.multiset_eq (bot_eq (op aconv))))
  val ms_lit_g =
    apply2 ms_of_lit
    #>
    Jeha_Order.multiset_is_greater_reference
      (Jeha_Order.multiset_is_greater_reference
        (bot_ord Jeha_Order.kbo #> curry op= (SOME GREATER))
        (bot_eq (op aconv)))
      (* (Jeha_Order.multiset_eq (bot_eq (op aconv))) *)
      (Jeha_Order.multiset_eq (bot_eq (Jeha_Order.kbo #> curry op= (SOME EQUAL))))
  fun are_equal_lit_ords (l, r) =
    case JLit.kbo (l, r) of
      SOME LESS => ms_lit_g (r, l)
    | SOME GREATER => ms_lit_g (l, r)
    | SOME EQUAL => ms_lit_eq (l, r)
    | NONE => not (ms_lit_eq (l, r)) andalso not (ms_lit_eq (r, l))
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
    | NONE =>
        not (
          ms_lit_generic_g cmp (l, r) orelse
          ms_lit_generic_g cmp (r, l) orelse
          ms_lit_generic_eq (l, r)
        )
  val are_equal_lit_int_ords = are_equal_lit_generic_ords (SOME o int_ord)
\<close>

ML_val \<open>
  (* val (l1, l2) = ((2, 3, false), (4, 1, true));  *)
  val (l1, l2) = ((1, 1, false), (2, 1, true)); 
  val (l1_ms, l2_ms) = apply2 ms_of_lit (l1, l2);
  (* NOTE multisets of true and false are always disjoint *)
  val l1_g_l2 = ms_lit_generic_g (SOME o int_ord) (l1, l2);
  val l2_g_l1 = ms_lit_generic_g (SOME o int_ord) (l2, l1);
  val l1_kbo_l2 = JLit.kbo_generic (SOME o int_ord) (l1, l2);
  val l2_kbo_l1 = JLit.kbo_generic (SOME o int_ord) (l2, l1);
  \<^assert> (are_equal_lit_int_ords (l1, l2))
\<close>


declare [[speccheck_max_success = 100000]]
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

declare [[speccheck_max_success = 1000]]
declare [[show_types]]

ML \<open>
  (* val show_lit = JLit.pretty_lit' @{context} *)
  fun set_params gen = gen 2 2 (1, 1, 1, 0) 4 4
  val term_gen_set = JGen.term_gen' @{context} |> set_params
  val term_pair_gen_set = JGen.term_pair_gen' @{context} |> set_params
  val lit_gen_set = JGen.lit_gen' @{context} |> set_params
  val check_lit = check JGen.show_lit (lit_gen_set)
  val check_lit_pair =
    check (Show.zip JGen.show_lit JGen.show_lit) (Gen.zip lit_gen_set lit_gen_set)
  val lit_test = Lecker.test_group @{context} (Random.new ()) [
    Prop.prop (are_equal_lit_ords) |> check_lit_pair "some lits"
  ]
\<close>

ML_val \<open>
  (* val (Ta, Tb) = (@{typ_pat "?'a"}, @{typ_pat "?'b"}); *)
  val (Ta, Tb) = (@{typ "'a"}, @{typ "'b"})
  val x = Var (("x", 0), Ta);
  val [c, d, e] = map (fn n => Free (n, Ta)) ["c", "d", "e"] 
  val l1 = (x, c, false); 
  val l2 = (d, e, true);
  val _ = writeln ("comparing " ^ JLit.pretty_lit @{context} l1 ^ " (l1) with " ^ JLit.pretty_lit @{context} l2 ^ " (l2)")
  val comp_gen = JLit.kbo (l1, l2);
  (* at least it's self consistent: *)
  val comp_gen_swapped = JLit.kbo (l2, l1);
  val l1_greater = ms_lit_g (l1, l2);
  val l2_greater = ms_lit_g (l2, l1);
  \<^assert> (are_equal_lit_ords (l1, l2))
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

end
