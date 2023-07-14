theory experiments

imports Main HOL.Hilbert_Choice

begin

notation (output) "Pure.prop" ("#_" [1000] 1000)

(* 

ML_file "jeha_tactic.ML";

ML \<open>
  fun pwrite_term ctxt t = Pretty.writeln (Syntax.pretty_term ctxt t)
  fun pwrite_type ctxt typ = Pretty.writeln (Syntax.pretty_typ ctxt typ)
  (* fun pwrite_terms ctxt terms =  *)
  (*   Pretty.writeln (Pretty.block (Pretty.commas (map (Syntax.pretty_term ctxt) terms))) *)
   fun pwrite_terms ctxt terms =
     terms
     |> map (Syntax.pretty_term ctxt)
     |> Pretty.commas |> Pretty.block |> Pretty.writeln
  val example_terms = [@{term "x::prop"}, @{term "y::prop"}]
  val _ = pwrite_terms @{context} example_terms
  fun pwrite_terms_typed ctxt t =
    pwrite_terms (Config.put show_types true ctxt) t
  val _ = pwrite_terms_typed @{context} example_terms
  fun pwrite_cterm ctxt ct = pwrite_term ctxt (Thm.term_of ct)
  fun config_put_many_bool ctxt options =
    List.foldr (fn (option, ctxt) => Config.put option true ctxt) ctxt options
  fun verbose_of ctxt = config_put_many_bool ctxt
    [show_types, show_brackets, show_markup, (* show_sorts, *) show_structs]
  fun pwrite_thm ctxt thm = pwrite_term ctxt (Thm.prop_of thm)
  val _ = pwrite_thm @{context} @{thm conjI}
  val _ = pwrite_thm @{context} @{thm conjE}
  val _ = fastype_of
  val _ = Variable.variant_frees
  val _ = fold_aterms
  val _ = Name.declare
  fun apply_fresh_args term ctxt =
    term
    |> fastype_of
    |> binder_types
    |> map (pair "z")
    |> Variable.variant_frees ctxt [term]
    |> map Free
    |> curry list_comb term
  val _ =
    let
      val term = @{term "P::nat \<Rightarrow> int \<Rightarrow> unit \<Rightarrow> bool"}
      val ctxt = verbose_of @{context}
    in
      pwrite_term ctxt term;
      apply_fresh_args term ctxt |> pwrite_term ctxt
    end
  val term_zaa = @{term "za::'a \<Rightarrow> 'b \<Rightarrow> 'c"}
  val _ = pwrite_term (verbose_of @{context}) term_zaa
  val _ = pwrite_term @{context} (apply_fresh_args term_zaa @{context})
  val _ = pwrite_thm @{context} @{thm allI}
  val _ = pwrite_thm (verbose_of @{context}) @{thm allI}
  val _ = map (pwrite_thm @{context}) @{thms conj_ac}
  val _ = pwrite_thm @{context} @{thm refl}
  val _ = pwrite_thm @{context} @{thm eq_reflection}
  val _ = pwrite_thm @{context} @{thm refl[THEN eq_reflection]}
  val c = Meson.make_cnf [] @{thm conjI} @{context}
  val foo_thm = @{prop "(Q \<Longrightarrow> False) \<Longrightarrow> Q \<Longrightarrow> P"}
  (* val _ = pwrite_thm @{context} foo_thm *)
  (* val d = Meson.make_clauses @{context} [foo_thm] *)
  val x = fold_aterms
  structure FooRules = Named_Thms (
    val name = @{binding "foo"}
    val description = "theorems for foo")
  val t = @{term "\<lambda> x y . x y"}
  (* eta-contracted to \<lambda> x . x but the type annotation x : 'a \<Rightarrow> 'b is kept! *)
  val _ = pwrite_term (verbose_of @{context}) t
  (* no beta reduction. why? *)
  val _ = pwrite_term (verbose_of @{context}) (t $ @{term "\<lambda> x . x"})
  (* beta reduction *)
  val _ = let
    val redex = @{term "\<lambda> (x::int) (y::int) . x"}
    val arg1 = @{term "1::int"}
    val arg2 = @{term "2::int"}
  in
    pwrite_term (verbose_of @{context}) (redex $ arg1 $ arg2)
  end
  (* but here there is beta reduction *)
  val _ = let
    (* refined version of t above *)
    val redex = @{term "\<lambda> (x::int \<Rightarrow> int) (y::int) . x y"}
    val arg1 = @{term "\<lambda> (z::int) . z"}
    val arg2 = @{term "2::int"}
  in
    pwrite_term (verbose_of @{context}) (redex $ arg1 $ arg2)
  end
  (* also no beta reduction *)
  val _ = let
    (* refined version of t above *)
    val redex = @{term "\<lambda> (x::'a \<Rightarrow> 'a) (y::'a) . x y"}
    val arg1 = @{term "\<lambda> (z::int) . z"}
    val arg2 = @{term "2::int"}
  in
    pwrite_term (verbose_of @{context}) (redex $ arg1 $ arg2) 
  end
  (* here there is beta reduction, in a polymorphic setting *)
  val _ = pwrite_term (verbose_of @{context}) (@{term "\<lambda> x::'a \<Rightarrow> 'a . x"} $ @{term "\<lambda> y::'a . y"})
  (* conclusion: no beta reduction if it requires restricting the polymorphic
  type of the function (no implicit down casting?) *)
  (* Exercise 3.1.1 *)
  val case_term = @{term "case x of 0 \<Rightarrow> 0 | Suc y \<Rightarrow> y"}
  (* this results in
    Const ("Nat.nat.case_nat", "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat")
      $ Const ("Groups.zero_class.zero", "nat")
      $ Abs ("y", "nat", Bound 0)
      $ Free ("x", "nat")
    : term
  *)
  val xy_to_pyx = @{term "\<lambda> (x, y) . P y x"}
  (* guess:
    Abs("z", "'a * 'b", Var("P", "'a * 'b \<Rightarrow> prop") $ (proj_2 z) $ (proj_1 $ z))
    actual:
    Const ("Product_Type.prod.case_prod", "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c")
      $ Abs ("x", "'a", Abs ("y", "'b", Free ("P", "'b \<Rightarrow> 'a \<Rightarrow> 'c")
      $ Bound 0 $ Bound 1))
    : term
    observation: P is Free, not Var, uses cases instead of projections
  *)
\<close>
declare [[ML_print_depth = 50]]
ML \<open>
  val set_of_singletons = @{term " { [x] | x . x \<le> -2 }"}
  (* this results in
    Const ("Set.Collect", "('a list \<Rightarrow> bool) \<Rightarrow> 'a list set")
      $ Abs ("uu_", "'a list",
          Const ("HOL.Ex", "('a \<Rightarrow> bool) \<Rightarrow> bool")
            $ Abs ("x", "'a",
                Const ("HOL.conj", "bool \<Rightarrow> bool \<Rightarrow> bool")
                  $ (Const ("HOL.eq", "'a list \<Rightarrow> 'a list \<Rightarrow> bool")
uu_ :                 $ Bound 1
                      $ (Const ("List.list.Cons", "'a \<Rightarrow> 'a list \<Rightarrow> 'a list") $ Bound 0 $ Const ("List.list.Nil", "'a list"))
                    )
                  $ (Const ("Orderings.ord_class.less_eq", "'a \<Rightarrow> 'a \<Rightarrow> bool")
x :                   $ Bound 0
   /                  $ (Const ("Groups.uminus_class.uminus", "'a \<Rightarrow> 'a")
-2 |                      $ (Const ("Num.numeral_class.numeral", "num \<Rightarrow> 'a")
   \                          $ (Const ("Num.num.Bit0", "num \<Rightarrow> num") $ Const ("Num.num.One", "num"))
                            )
                        )
                    )
              )
        )
    : term
  
  essentially: \<exists> x :: 'a . uu_ = [x] \<and> x \<le> -2
  *)
  val _ = pwrite_term @{context} set_of_singletons
\<close>
declare [[ML_print_depth = 50]]
ML \<open>
  val term_and_prop = [@{term "P x"}, @{prop "P x"}]
  val _ = pwrite_terms (verbose_of @{context}) term_and_prop
  val two_meta_implications = [@{term "P x \<Longrightarrow> Q x"}, @{prop "P x \<Longrightarrow> Q x"}]
  val _ = pwrite_terms (verbose_of @{context}) two_meta_implications
  val one_implication = @{term "P x \<longrightarrow> Q x"}
  val one_meta_implication = @{prop "P x \<longrightarrow> Q x"}
\<close>
(* changing the typ pretty printer *)
ML \<open>
  local
    fun pp_pair (x, y) = Pretty.list "(" ")" [x, y]
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
  end;
  ML_system_pp (fn _ => fn _ => Pretty.to_polyml o raw_pp_typ);
  val some_typ = @{typ "'a \<Rightarrow> 'b"}
  val _ = pwrite_type @{context} some_typ
  val list_typ = @{typ "'a list"}
  val _ = pwrite_type @{context} some_typ
  val bool_typ = @{typ "bool"}
  val int_typ = @{typ "int"}
  val _ = pwrite_type @{context} (Type ("Int.int", []));
  (* reset to default pretty printer *)
  ML_system_pp (fn depth => fn _ => ML_Pretty.to_polyml o Pretty.to_ML depth o Proof_Display.pp_typ Theory.get_pure);
\<close>
ML \<open>
  fun make_imp P Q =
    let
      val x = Free ("x", @{typ nat})
    in
      Logic.all x (Logic.mk_implies (P $ x, Q $ x))
    end
  val forall_p_imp_q = make_imp @{term "S"} @{term "T"}
  val _ = pwrite_term @{context} forall_p_imp_q
  fun wrong_make_imp P Q = @{prop "\<And> (x::nat) . P x \<Longrightarrow> Q x"}
  val wrong_forall_p_imp_q = wrong_make_imp @{term "S"} @{term "T"}
  (* same name but different types *)
  val no_abstraction = let
    val x_a = @{term "x::nat"}
    val t = @{term "(P::'a \<Rightarrow> bool) x"}
  in
    lambda x_a t
  end
  (* pretty printer distinguishes the variables! *)
  val _ = pwrite_term @{context} no_abstraction
  val maybe_abstraction = let
    val x_aa = @{term "x::'a \<Rightarrow> 'a"}
    val t = @{term "(P::('b \<Rightarrow> 'b) \<Rightarrow> bool) x"}
  in
    lambda x_aa t
  end
  (* still distinguished by pretty printer *)
  val _ = pwrite_term @{context} maybe_abstraction
  (* conclusion: the terms need to have exactly equal types, even types that
  feel alpha convertible are not the same (alpha convertibilty doesn't really
  make sense because polymorphic variables like 'a, 'b are TFree, i.e. not
  bound) *)

  (* this is kind of weird: *)
  val wrong_substituted_bound = subst_free [(Bound 0, Free ("bad", @{typ bool}))] @{term "\<lambda> x . x"}
  (* but probably justified since it doesn't make sense to speak of a free
  occurence of Bound 0. But maybe subst_free should reject such input?
  Basically there is nothing in the implementation of subst_free that checks if
  the expression being replaced is free, it all relies on the assumption that
  the user would never want to replace a "free" orccurence of Bound i for some
  other term *)
  (* also doesn't do de Bruijn shifting *)
  val no_shifting = subst_free [(Bound 0, Bound 3)] @{term "\<lambda> x . x"}
  
  (* *)
  val correct_no_substitution = subst_bounds ([Free("bad", @{typ bool})], @{term "\<lambda> x . x"})
  (* substitutes and shifts down bounds that are still loose after substitution *)
  val correct_substituted_loose_bound = subst_bounds ([Free("good", @{typ bool})], (Bound 0 $ Bound 1))
  (* Bound 3 is correctly shifted up when passing the binder *)
  val correct_db_shift =
    subst_bounds ([Bound 3, Free("bad", @{typ bool})], Abs("", @{typ int}, Bound 1 $ Bound 0))
  fun strip_alls t =
    let 
      fun aux (x, T, t) = strip_alls t |>> cons(Free (x, T))
    in
      case t of
        Const (@{const_name All}, _) $ Abs body => aux body
      | _ => ([], t)
    end
  val term_with_alls = @{term "\<forall> x . \<forall> y . P x y"}
  val _ = pwrite_term @{context} term_with_alls
  val (stripped_vars, stripped_term) = strip_alls term_with_alls
  (* need rev for correct order! *)
  val stripped_term_with_named_vars = subst_bounds (rev stripped_vars, stripped_term);
  fun build_alls ([], t) = t
    | build_alls (Free (x, T) :: vs, t) = 
        Const (@{const_name "All"}, (T --> @{typ bool}) --> @{typ bool})
          $ Abs (x, T, build_alls (vs, t))
  val with_rebuilt_alls = build_alls (stripped_vars, stripped_term)
  val _ = pwrite_term @{context} with_rebuilt_alls
  val _ = @{term HOL.All}
  val (whatsthis, (andthis, new_ctxt)) =
  let
    val body = Abs ("x", @{typ nat}, Bound 0 $ Free ("x", @{typ nat}))
  in 
    (Term.dest_abs_fresh "y" body, Variable.dest_abs body @{context})
  end
  val some_list = @{term "[1,2,3,4]"}
  val _ = pwrite_term @{context} some_list
  fun hol_list_to_ml_list (Const (@{const_name Nil}, _)) = []
    | hol_list_to_ml_list (Const (@{const_name Cons}, _) $ x $ tl) = x::hol_list_to_ml_list tl
  val ml_list_with_hol_nums = hol_list_to_ml_list some_list
  fun hol_num_to_ml_num (Const (@{const_name Groups.one_class.one}, _)) = 1
    | hol_num_to_ml_num (Const (@{const_name numeral}, _) $ raw_num) =
      let
        fun raw_num_to_ml_num (Const (@{const_name num.One}, _)) = 1
          | raw_num_to_ml_num (Const (@{const_name num.Bit0}, _) $ rest) = 2 * raw_num_to_ml_num rest
          | raw_num_to_ml_num (Const (@{const_name num.Bit1}, _) $ rest) = 2 * raw_num_to_ml_num rest + 1
          | raw_num_to_ml_num _ = error "bad"
      in
        raw_num_to_ml_num raw_num
      end
    | hol_num_to_ml_num _ = error "badder"
  val not_one = @{term 1}
  val this_one::_ = ml_list_with_hol_nums
  val one = let val hol_one::_ = ml_list_with_hol_nums in hol_num_to_ml_num hol_one end
  val ml_list = map hol_num_to_ml_num ml_list_with_hol_nums
\<close>

ML \<open>
  (* Ex. 3.2.5 *)
  fun deBruijn 0 = @{term True}
    | deBruijn n =
      let
        fun p i =  @{term "P::nat\<Rightarrow>bool"} $ HOLogic.mk_number @{typ nat} i
        fun rhs n = fold (fn i => fn t => HOLogic.mk_conj (p i, t)) (n-1 downto 1) (p n)
        fun lhs n =
          let
            fun lhs_lhs_conjunct i = HOLogic.mk_imp (HOLogic.mk_eq (p i, p ((i + 1) mod n)), rhs n)
            val lhs_lhs = fold (fn i => fn t => HOLogic.mk_conj (lhs_lhs_conjunct i, t)) (n-1 downto 1) (lhs_lhs_conjunct n)
          in HOLogic.mk_imp (lhs_lhs, rhs n) end
      in
        HOLogic.mk_imp (lhs n, rhs n)
      end
  val nthree = deBruijn 3
  val _ = pwrite_term @{context} nthree
\<close>

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
  fun pretty_helper aux env = env
    |> Vartab.dest
    |> map aux
    |> map (fn (s1, s2) => Pretty.block [s1, Pretty.str " := ", s2])
    |> Pretty.enum "," "[" "]"
    |> Pretty.writeln
  fun pwrite_tyenv ctxt tyenv =
  let
    fun get_typs (v, (s, T)) = (TVar (v, s), T)
    val print = apply2 (Syntax.pretty_typ ctxt)
  in
    pretty_helper (print o get_typs) tyenv
  end

  (* you have to make variables distinct yourself, obiously *)
  (* the result is not a simultaneous substitution, it's in triangular form *)
  val (tyenv_unif, _) = let
    val ty1 = @{typ_pat "?'a * ?'b"}
    val ty2 = @{typ_pat "?'b list * nat"}
  in
    Sign.typ_unify @{theory} (ty1, ty2) (Vartab.empty, 0)
  end;
  pwrite_tyenv @{context} tyenv_unif;
  val (tyenvs, _) = let
    val tys1 = (@{typ_pat "?'a"}, @{typ_pat "?'b list"})
    val tys2 = (@{typ_pat "?'b"}, @{typ_pat "nat"})
  in
    fold (Sign.typ_unify @{theory}) [tys1, tys2] (Vartab.empty, 0)
  end;
  pwrite_tyenv @{context} tyenvs;
  Envir.norm_type tyenv_unif @{typ_pat "?'a * ?'b"}
\<close>

class s1
class s2

ML \<open>
  val (tyenv, index) = let
    val ty1 = @{typ_pat "?'a::s1"}
    val ty2 = @{typ_pat "?'b::s2"}
  in
    Sign.typ_unify @{theory} (ty1, ty2) (Vartab.empty, 0)
  end;
  pwrite_tyenv (verbose_of @{context}) tyenv;
\<close>

ML \<open>
  val tyenv_match = let
    val pat = @{typ_pat "?'a * ?'b"}
    val ty = @{typ_pat "bool list * nat"}
  in
    Sign.typ_match @{theory} (pat, ty) Vartab.empty
  end;
  pwrite_tyenv @{context} tyenv_match;
  Envir.subst_type tyenv_match @{typ_pat "?'a * ?'b"};
\<close>



ML \<open>
  fun pwrite_env ctxt env =
  let
    fun get_trms (v, (T, t)) = (Var (v, T), t)
    val print = apply2 (Syntax.pretty_term ctxt)
  in
    writeln "env:"; pretty_helper (print o get_trms) env
  end;

  val (_, fo_env) = let
    val fo_pat = @{term_pat "(?X::(nat\<Rightarrow>nat\<Rightarrow>nat)\<Rightarrow>bool) ?Y"}
    val trm_a = @{term "P::(nat\<Rightarrow>nat\<Rightarrow>nat)\<Rightarrow>bool"}
    val trm_b = @{term "\<lambda>a b. (Q::nat\<Rightarrow>nat\<Rightarrow>nat) b a"}
    val init = (Vartab.empty, Vartab.empty)
  in
    (* ?X ?Y =? P \<lambda>a b. Q b a *)
    Pattern.first_order_match @{theory} (fo_pat, trm_a $ trm_b) init
  end;
  pwrite_env @{context} fo_env;
  val xy = let 
    val trm = @{term_pat "(?X::(nat\<Rightarrow>nat\<Rightarrow>nat)\<Rightarrow>bool) ?Y"}
  in
    Envir.subst_term (Vartab.empty, fo_env) trm |> pwrite_term @{context}
  end;
  let
    val trm1 = @{term_pat " \<lambda>x y. g (?X y x) (f (?Y x))"}
    val trm2 = @{term_pat " \<lambda>u v. g u (f u)"}
    val init = Envir.empty 0
    val env = Pattern.unify (Context.Proof @{context}) (trm1, trm2) init
  in
    (* Question: why these types, and not something more restricted,
    e.g. a -> a for the identity instead of a -> f? *)
    pwrite_env (verbose_of @{context}) (Envir.term_env env)
  end;

  val uni_seq =
  let
    val trm1 = @{term_pat "?X ?Y"}
    val trm2 = @{term_pat "f a"}
    val init = Envir.empty 0
  in
    Unify.unifiers (Context.Proof @{context}, init, [(trm1, trm2)])
  end;
  Seq.list_of (Seq.map (fn (uni_env, _) => pwrite_env @{context} (Envir.term_env uni_env)) uni_seq);
  writeln "ffs: ";
  Seq.list_of (Seq.map (fn (_, fpairs) => map (fn (t1, t2) => pwrite_terms @{context} [t1, t2]) fpairs) uni_seq);
\<close>

ML \<open>
  fun prep_trm ctxt (x, (T, t)) =
    ((x, T), Thm.cterm_of ctxt t)
  fun prep_ty ctxt (x, (S, ty)) =
    ((x, S), Thm.ctyp_of ctxt ty)
  fun matcher_inst ctxt pat trm i =
  let
    val univ = Unify.matchers (Context.Proof ctxt) [(pat, trm)]
    val env = nth (Seq.list_of univ) i
    val tenv = Vartab.dest (Envir.term_env env)
    val tyenv = Vartab.dest (Envir.type_env env)
  in
    (TVars.make (map (prep_ty ctxt) tyenv), Vars.make (map (prep_trm ctxt) tenv))
  end;

  pwrite_term @{context} (Thm.prop_of @{thm spec});

  
  val pat = Logic.strip_imp_concl (Thm.prop_of @{thm spec})
  val term = @{term "Trueprop (Q True)"}
  val spec_unifs = Seq.list_of (Unify.matchers (Context.Proof @{context}) [(pat, term)]);
  writeln "spec_unifs:";
  map (fn uni_env => pwrite_env @{context} (Envir.term_env uni_env)) spec_unifs;
  (* Question: what is the difference between unifiers with idxs 1 and 3? *)
  val good_inst = matcher_inst @{context} pat term 1;
  val good_spec = Drule.instantiate_normalize good_inst @{thm spec};
\<close>

ML \<open>
  val plus = Const (@{const_name "plus"}, dummyT);
  val plus_typed = Syntax.check_term @{context} plus;
\<close>

ML \<open>
  val abc = Thm.cterm_of @{context} @{term "(a::nat) + b = c"};
  @{cterm "(a::nat) + b = c"};
  pwrite_term (verbose_of @{context}) (Thm.term_of abc);
  let
    val natT = @{typ "nat"}
    val zero = @{term "0::nat"}
    val plus = Const (@{const_name plus}, [natT, natT] ---> natT)
  in
    Thm.cterm_of @{context} (plus $ zero $ zero)
  end;
  pwrite_type (verbose_of @{context}) (Thm.typ_of (Thm.ctyp_of @{context} (@{typ nat} --> @{typ bool})));
  Thm.apply @{cterm "P::nat \<Rightarrow> bool"} @{cterm "3::nat"};
  let
    val chead = @{cterm "P::unit \<Rightarrow> nat \<Rightarrow> bool"}
    val cargs = [@{cterm "()"}, @{cterm "3::nat"}]
  in
    Drule.list_comb (chead, cargs)
  end;
  val my_thm =
  let
    val assm1 = @{cprop "\<And>(x::nat). P x \<Longrightarrow> Q x"}
    val assm2 = @{cprop "(P::nat \<Rightarrow> bool) t"}
    val Pt_implies_Qt = Thm.assume assm1 |> Thm.forall_elim @{cterm "t::nat"}
    val Qt = Thm.implies_elim Pt_implies_Qt (Thm.assume assm2)
  in
    Qt |> Thm.implies_intr assm2 |> Thm.implies_intr assm1
  end;
  writeln "my_thm: "; pwrite_thm (verbose_of @{context}) my_thm;
  (* make free variables in theorem schematic variables: *)
  val my_thm_vars =
  let
    val ctxt0 = @{context}
    (* introducing new schematic variables changes the context to ctxt1 *)
    val (_, ctxt1) = Variable.add_fixes ["P", "Q", "t"] ctxt0
  in
    (* export my_thm as interpreted in ctxt1 into the outer context ctxt0 (?) *)
    singleton (Proof_Context.export ctxt1 ctxt0) my_thm
  end;
  let
    val eq = @{thm True_def}
  in
    (Thm.lhs_of eq, Thm.rhs_of eq)
    |> apply2 (YXML.content_of o Pretty.string_of o (Syntax.pretty_term @{context}) o Thm.term_of)
  end;
\<close>
(* Question: Whats' going on here in Variable.ML:461 (fun add_fixes_binding)?

    val (xs', names') =
      if is_body ctxt then fold_map Name.variant xs names |>> map Name.skolem
      else (xs, fold Name.declare xs names);
  
  When we're not in inner_body mode, we just declare the xs 
*)

lemma
  shows foo_test1: "A \<Longrightarrow> B \<Longrightarrow> C"
  and foo_test2: "A \<longrightarrow> B \<longrightarrow> C" sorry

ML \<open>
  (* object logic to meta logic: rulify *)
  Object_Logic.rulify @{context} @{thm foo_test2};
  (* meta logic to object logic: atomize *)
  let
    val thm = @{thm foo_test1}
    val meta_eq = Object_Logic.atomize @{context} (Thm.cprop_of thm)
  in
    Raw_Simplifier.rewrite_rule @{context} [meta_eq] thm
  end;
  fun atomize_thm ctxt thm =
  let
    (* flex-flex pairs play a role in Thm.forall_intr_vars as part of the eigenvariable condition! *)
    val thm' = Thm.forall_intr_vars thm
    val thm'' = Object_Logic.atomize ctxt (Thm.cprop_of thm')
  in
    Raw_Simplifier.rewrite_rule ctxt [thm''] thm'
  end;
  val list_induct = @{thm list.induct};
  val list_induct_atomized_proper = atomize_thm @{context} @{thm list.induct};
  (* compare the naïve *)
  val list_induct_atomized_naive =
    Raw_Simplifier.rewrite_rule @{context}
      [(Object_Logic.atomize @{context} (Thm.cprop_of @{thm list.induct}))]
      @{thm list.induct};
  (* calling forall_intr_vars now yields meta-foralls *)
  val list_induct_atomized_naive_foralls = Thm.forall_intr_vars list_induct_atomized_naive;
  (* Question: Do foralls under implications have anything to do with rank-n polymorphism? (don't
  think so) *)
  @{const_name "HOL.eq"};
  @{term "1 \<noteq> 3"};
  @{term "True = False"};
  @{term "True \<longrightarrow> False"};
  @{term "\<forall> x . True"};
  (* Why is \<not> represented as HOL.Not despite being defines as not_def: "\<not> P \<equiv> P \<longrightarrow> False",
  what role do the definitions play? *)
  @{term "\<not> True"};
  @{typ "'a \<Rightarrow> bool"};
  @{term "(0::nat) + 0"};
  append [1,2] [3,4];
  uncurry cons o strip_comb;
  @{term "x \<longleftrightarrow> y"}
\<close>

ML_file "jeha.ML";

(* declare [[ML_exception_trace = true]] *)
ML \<open>
  val quick_sig = ["a", "b", "f", "g", "h", "p", "q"]
  fun free_to_const (t as (Free (name, T))) = if exists (curry (op =) name) quick_sig then Const (name, T) else t
    | free_to_const t = t
  fun const_to_free (t as (Const (name, T))) = if exists (curry (op =) name) quick_sig then Free (name, T) else t
    | const_to_free t = t
  val term_with_subterms = @{term "f (g (\<not> p)) (\<forall> x . q) (y a) (\<lambda> x . h b)"};
  pwrite_term @{context} term_with_subterms;
  val tposs = Jeha.green_tposs_of (map_aterms free_to_const term_with_subterms);
  val green_subterms = map (Jeha.subterm_at_tpos term_with_subterms) tposs;
  fun pwrite_quicksig ctxt = pwrite_term ctxt o (map_aterms const_to_free);
  writeln "greens:"; map (pwrite_quicksig @{context}) green_subterms;
  val non_green_subterms = Jeha.fold_non_greens cons (map_aterms free_to_const term_with_subterms) [];
  writeln "nongreens:"; map (pwrite_quicksig @{context}) non_green_subterms;
  (* val unnormed = @{term "\<lambda> y . \<exists> x . g x y (z y) (f x)"}; (* don't rewrite: WORKS *) *)
  (* Question: Why does a lone quantifier not make sense to isabelle? (can't be parsed using @{term ...} *)
  val unnormed = Const (@{const_name "HOL.Ex"}, @{typ "('a \<Rightarrow> bool) \<Rightarrow> bool"}) (* rewrite: WORKS *)
  (* val unnormed = @{term "\<exists> x . x a"}; (* rewrite: WORKS *) *)
  (* val unnormed = @{term "\<forall> x . f (\<lambda> y . x)"} (* rewrite: WORKS *); *)
  val normed = map_aterms const_to_free (Jeha.norm_quantifier_poly_eq (map_aterms free_to_const unnormed));
  writeln "Q\<^sub>\<approx>:"; pwrite_term @{context} unnormed; pwrite_term @{context} normed;
  CONTEXT_TACTIC
\<close>


ML \<open>
  type var_balance = { counts: int Vartab.table, pos_balances: int, neg_balances: int};
  val (c : var_balance -> int Vartab.table) = #counts;
\<close>


*)


ML \<open>
  val proporp = @{term "PROP Q"}
  val aborbad = @{prop "a = b \<or> False"}
\<close>

ML \<open>
fun my_print_tac ctxt thm =
let
  val _ = tracing "my_print_tac: "
  val _ = tracing (Pretty.string_of (Syntax.pretty_term ctxt (Thm.prop_of thm)))
in
  Seq.single thm
end
\<close>

theorem
  assumes a
  shows "A \<Longrightarrow> A"
proof - (* dash is the "null method that does nothing to the goal" *)
  assume "A"
  show "A" by fact
qed

find_theorems "?P \<Longrightarrow> ?Q" name:imp

theorem a_imp_a: "A \<Longrightarrow> B \<Longrightarrow> A" sorry
(* proof -
  ML_val \<open>
    val goal = #goal @{Isar.goal}
    val goal' = Clasimp.auto_tac @{context} goal |> Seq.pull
  \<close> *)

(*
ML \<open>
  fun excluded_middle P =
    \<^instantiate>\<open>P in lemma (open) \<open>P \<Longrightarrow> \<not> P \<Longrightarrow> False\<close> by (rule notE)\<close>

  val x = 3
\<close>
*)

ML \<open>
  val someosme = @{term "SOME x . x = 3"}
  val f = @{cprop "True"}
  val goal = Goal.init f
  val proof = Clasimp.auto_tac @{context} goal;
  val SOME (first, rest) = Seq.pull proof
  val second = Seq.pull rest

\<close>

(*
ML \<open>
  val ctxt = @{context}
  val A = @{cterm "A :: bool"}
  (* val ([A], ctxt) = Variable.add_fixes ["A"] ctxt *)
  val t = \<^instantiate>\<open>A in lemma (open) \<open>A \<Longrightarrow> A\<close> by auto\<close>
  val t' = Goal.protect 2 t
  val t'' = Clasimp.auto_tac @{context} t'
  val SOME t''' = Seq.pull t''
\<close>
*)

thm Pure.reflexive
thm Pure.equal_intr_rule
thm HOL.atomize_not
thm Pure.equal_elim_rule1
thm disjE
thm disjI1
thm HOL.de_Morgan_disj


(* declare [[show_types, simp_trace]] *)

(* have just states a fact, show refines a goal *)  

theorem abimp : "(Trueprop ((a :: bool) \<or> b)) \<equiv> (\<not> a \<Longrightarrow> \<not> b \<Longrightarrow> False)"
proof (rule Pure.equal_intr_rule)
  show "a \<or> b \<Longrightarrow> \<not> a \<Longrightarrow> \<not> b \<Longrightarrow> False" (* pick which goal we want to prove (1.) *)
  proof - (* don't apply any introduction rule *)
    assume "a \<or> b" (* introduce assumption *)
    then show "(\<not> a) \<Longrightarrow> (\<not> b) \<Longrightarrow> False"
    proof (rule disjE) (* refine goal with disjE. use `elim` instead of `rule` for repeated application of disjE *)
      have "(Trueprop (\<not> a)) \<equiv> (a \<Longrightarrow> False)"
        apply (rule Pure.symmetric)
        apply (rule HOL.atomize_not)
        done
      then show "\<not> a \<Longrightarrow> a \<Longrightarrow> False"
        apply (rule Pure.equal_elim_rule1)
        by assumption
    next
      show "\<not> b \<Longrightarrow> b \<Longrightarrow> False" by contradiction
    qed
  qed
next
  assume "\<not> a \<Longrightarrow> \<not> b \<Longrightarrow> False"
  then show "a \<or> b"
  proof (cases ?thesis)
    assume "a \<or> b"
    then show ?thesis by assumption
  next
    assume 0: "\<not> (a \<or> b)"
    have 1: "\<not> a \<and> \<not> b"
      apply (rule Pure.equal_elim_rule1[where phi = "\<not> (a \<or> b)"])
    proof -
      from 0 show "\<not> (a \<or> b)" by assumption
    next
      (* for atomize we need \<equiv> :: bool \<rightarrow> bool \<rightarrow> prop, but for the goal we need prop \<rightarrow> prop \<rightarrow> prop *)
      (* Q: why can't atomize deal with "Trueprop (\<not> (a \<or> b)) \<equiv> Trueprop (\<not> a \<and> \<not> b)" ? *)
      have "\<not> (a \<or> b) \<equiv> \<not> a \<and> \<not> b"
        apply (atomize (full))
        apply (rule HOL.de_Morgan_disj)
        done
      from this show "Trueprop (\<not> (a \<or> b)) \<equiv> Trueprop (\<not> a \<and> \<not> b)" by (auto)
    qed
    from 1 have 2: "\<not> a"
      apply (rule HOL.conjunct1)
      done
    from 1 have 3: "\<not> b"
      apply (rule HOL.conjunct2)
      done
    assume "\<not> a \<Longrightarrow> \<not> b \<Longrightarrow> False"
    from 2 and 3 and this have False by (auto)
    from this show "a \<or> b" by (auto)
  qed
qed

theorem eres: "c \<or> u \<noteq> u \<Longrightarrow> c"
  apply (auto)
  done

thm ccontr


lemma disj_swap:
  shows "P \<or> Q \<Longrightarrow> Q \<or> P"
apply (erule disjE)
apply (rule disjI2)
apply (assumption)
apply (tactic \<open>my_print_tac @{context}\<close>)
apply (rule disjI1)
apply (tactic \<open>my_print_tac @{context}\<close>)
apply (assumption)
done

ML \<open>
fun pretty_cterm ctxt = Syntax.pretty_term ctxt o Thm.term_of

fun pretty_terms ctxt terms =
  terms
  |> map (Syntax.pretty_term ctxt)
  |> Pretty.commas |> Pretty.block

fun pretty_cterms ctxt = pretty_terms ctxt o map Thm.term_of

fun pretty_thm ctxt = Syntax.pretty_term ctxt o Thm.prop_of

fun pretty_thms ctxt = Pretty.block o Pretty.commas o map (pretty_thm ctxt)

fun foc_tac {context, params, prems, asms, concl, schematics} =
  let
    fun assgn1 f1 f2 xs =
      let
        val out = map (fn (x, y) => Pretty.enum ":=" "" "" [f1 x, f2 y]) xs
      in
        Pretty.list "" "" out
      end
    fun assgn2 f xs =
      assgn1 (fn (n,T) => Syntax.pretty_term context (Var (n,T))) f xs
    val pps = map (fn (s, pp) => Pretty.block [Pretty.str s, pp])
      [("params: ", assgn1 Pretty.str (pretty_cterm context) params),
      ("assumptions: ", pretty_cterms context asms),
      ("conclusion: ", pretty_cterm context concl),
      ("premises: ", pretty_thms context prems)]
      (* ("schematics: ", assgn2 (pretty_cterm context) (snd schematics)) ] *)
  in
    tracing (Pretty.string_of (Pretty.chunks pps)); all_tac
  end
\<close>

lemma test2:
  shows "(x = y) \<Longrightarrow> (y = z) \<longrightarrow> (x = z)"
apply (tactic \<open>Object_Logic.atomize_prems_tac @{context} 1\<close>)
apply (tactic \<open>my_print_tac @{context}\<close>)
apply (auto)
done

lemma test3:
  shows "(A \<Longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B"
apply (tactic \<open>my_print_tac @{context}\<close>)
apply (tactic \<open>Object_Logic.atomize_prems_tac @{context} 1\<close>)
apply (tactic \<open>my_print_tac @{context}\<close>)
apply (tactic \<open>resolve_tac @{context} @{thms ccontr} 1\<close>)
apply (tactic \<open>my_print_tac @{context}\<close>)
apply (auto)
done


lemma blbla:
  shows "P \<Longrightarrow> A \<Longrightarrow> P" and "D \<Longrightarrow> D"
apply (tactic \<open>my_print_tac @{context}\<close>)
apply (tactic \<open>SELECT_GOAL (my_print_tac @{context}) 2\<close>)
apply (tactic \<open>resolve_tac @{context} [ccontr] 2\<close>)
(* apply (tactic \<open>SELECT_GOAL (resolve_tac @{context} [ccontr] 1) 2\<close>) *)
apply (tactic \<open>my_print_tac @{context}\<close>)
(* apply (rule ccontr)
apply (tactic \<open>my_print_tac @{context}\<close>)
apply (tactic \<open>Subgoal.FOCUS foc_tac @{context} 1\<close>) *)
apply (auto)
done

notepad
begin
  fix x
  term x
  term y
  fix y
  term y
end


(* apply (tactic \<open>PRIMITIVE (Goal.restrict 1 1)\<close>) *)

theorem permute_this_thing: "A \<Longrightarrow> B \<Longrightarrow> C \<Longrightarrow> D \<Longrightarrow> E"
  sorry

ML \<open>
  val t = @{thm "permute_this_thing"}
  val p = Thm.permute_prems 0 2 t
  val pr = Thm.prop_of p
\<close>

find_theorems "x = y ==> y \<noteq> z ==> x \<noteq> z"

lemma trans_contra: "1 = y \<Longrightarrow> y \<noteq> 2 \<Longrightarrow> 1 \<noteq> 2" sorry

(* thm trans_contra *)

lemma efact_example: "C' \<Longrightarrow> u \<noteq> v' \<Longrightarrow> 2 \<noteq> 1 \<Longrightarrow> False" sorry

declare [[show_types]]

ML \<open>
  val t = @{term "a \<longrightarrow> b"}
  (* val thm = @{thm efact_example}
  val lm = @{thm trans_contra}
  val dup = lm RSN (3, thm) *)
\<close>


theorem eres_alt: "(\<not> c \<Longrightarrow> u = u \<Longrightarrow> False) \<Longrightarrow> c"
proof (rule ccontr)
  assume "\<not> c \<Longrightarrow> u = u \<Longrightarrow> False"
  then show "\<not> c \<Longrightarrow> False"


      (* apply (rule Pure.equal_elim_rule1[where psi = "\<not> a \<and> \<not> b"]) *)
      
      
    (* have "\<not> (a \<or> b) \<equiv> \<not> a \<and> \<not> b"
      apply (atomize (full))
      apply (rule HOL.de_Morgan_disj)
      done
    have "(Trueprop (\<not> (a \<or> b)) \<equiv> Trueprop (\<not> a \<and> \<not> b)) \<Longrightarrow> (\<not> (a \<or> b)) \<Longrightarrow> (\<not> a \<and> \<not> b)"
      apply (rule Pure.equal_elim_rule1[where phi = "\<not> (a \<or> b)"]) *)
      
      

      
      
      (* apply (tactic \<open> Object_Logic.rulify_tac @{context} 1 \<close>) *)
      
      
      
      
      
    
    (* assume "\<not> (a \<or> b)" and "\<not> a \<Longrightarrow> \<not> b \<Longrightarrow> False"
    then show "a \<or> b"
    proof - *)











(*
nongreens: 
f 
h b 
a 
y 
\<lambda>x. q 
All 
g 
Not 
p 
*)

(* Question: is Abs("x", @{typ nat}, Free "x") allowed? And what is it's meaning? *)



end