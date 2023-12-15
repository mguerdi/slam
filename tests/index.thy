theory "index"

imports "../jeha" SpecCheck.SpecCheck_Dynamic

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

ML_file \<open>../jeha_index.ML\<close>

setup \<open> Jeha_Common.term_schem_setup \<close>

ML \<open>
  val fps = [[], [1]]
  val terms =
    [ @{term_schem "?x :: int"}
    , @{term_schem "c :: int"}
    , @{term_schem "d :: int"}
    , @{term_schem "f(d) :: int"}
    , @{term_schem "f(?x) :: int"}
    , @{term "\<lambda> x . d"}
    ]
  val keys = map (Term_Index.compute_key fps) terms
  val index = fold (Term_Index.insert_term fps) terms Term_Index.empty
  val _ =
    Term_Index.fold
      (K true)
      [Jeha_Fingerprint.FOFree "f", Jeha_Fingerprint.AnonymousVar]
      (fn t => K (writeln (Jeha_Common.pretty_term @{context} t)))
      index
      ()
\<close>

ML_file \<open>../jeha_gen_term.ML\<close>

ML \<open>
  fun set_params gen = gen 2 2 (1, 1, 1, 0) 4 4
  val term_gen_set = JGen.term_gen' @{context} |> set_params 

  (* (weight_const, weight_free, weight_var, weight_bound) *)
  (* these weights achieve ~50 percent unifiability *)
  val term_pair_gen_set = JGen.term_pair_gen' @{context} |> set_params 

  val check_term = check (Show.term @{context}) term_gen_set

  fun show_termpair ctxt =
    let val pretty_term = Syntax.pretty_term ctxt
    in SpecCheck_Show.zip pretty_term pretty_term end

  val check_term_pair = check (show_termpair @{context}) term_pair_gen_set
\<close>

ML_val \<open>
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

end