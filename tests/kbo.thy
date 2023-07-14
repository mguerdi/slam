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
ML_file \<open>../jeha_order.ML\<close>

declare [[speccheck_max_success = 10]]
declare [[speccheck_num_counterexamples = 30]]
declare [[ML_print_depth = 100]]

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
check_dynamic @{context} "ALL s t. Jeha_Common.map_some rev_order (Jeha_Order.kbo (t, s)) = Jeha_Order.kbo (s, t)"
\<close>

ML_command \<open>
check_dynamic @{context} "ALL s t. (SOME EQUAL = Jeha_Order.kbo (s, t)) = (s aconv t)"
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
