(* see
  https://www.isa-afp.org/browser_info/current/AFP/ML_Unification/AFP/ML_Unification/Tests/tests_base.ML.html
and related *)

signature JGEN =
sig
  val term_gen : Proof.context -> int -> int -> int * int * int * int ->
    (int -> int -> int SpecCheck_Generator.gen) -> term SpecCheck_Generator.gen
  val term_pair_gen : Proof.context -> int -> int -> int * int * int * int ->
    (int -> int -> int SpecCheck_Generator.gen) ->
    (term * term) SpecCheck_Generator.gen
  val lit_gen : Proof.context -> int -> int -> int * int * int * int ->
    (int -> int -> int SpecCheck_Generator.gen) ->
    JLit.T SpecCheck_Generator.gen
    
  val term_gen' : Proof.context -> int -> int -> int * int * int * int -> int ->
    int -> term SpecCheck_Generator.gen
  val term_pair_gen' : Proof.context -> int -> int -> int * int * int * int ->
    int -> int -> (term * term) SpecCheck_Generator.gen
  val lit_gen' : Proof.context -> int -> int -> int * int * int * int ->
    int -> int -> JLit.T SpecCheck_Generator.gen
  
  val show_lit : JLit.T -> Pretty.T
    
  val check_lit : (JLit.T, 'a) SpecCheck_Generator.gen_state -> string ->
      (JLit.T) SpecCheck_Property.prop ->
      (Proof.context, 'a) Lecker.test_state
end

structure JGen : JGEN =
struct

structure Gen = SpecCheck_Generator

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

fun lit_gen ctxt nv ni weights num_args_gen =
  term_pair_gen ctxt nv ni weights num_args_gen
  |> Gen.map HOLogic.mk_eq
  |> Gen.zip (Gen.bernoulli 0.5)
  |> Gen.map (fn (b, t) => (if b then I else HOLogic.mk_not) t)
  |> Gen.map JLit.of_term

fun lit_gen' ctxt nv ni weights max_h max_args =
  lit_gen ctxt nv ni weights (num_args_gen max_h max_args)
  
(* val show_lit = JLit.pretty_lit' @{context} *)

val show_lit = @{make_string} #> Pretty.str

fun check_lit gen name prop ctxt =
  SpecCheck.check show_lit gen name prop ctxt

end