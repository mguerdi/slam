theory gen
imports
  Pure
  SpecCheck.SpecCheck_Dynamic
  SpecCheck.SpecCheck_Generators
begin

(* declare [[ML_debugger = true]]
declare [[ML_exception_trace = true]]
declare [[ML_exception_debugger = true]] *)

ML_file \<open>jeha_common.ML\<close>

ML \<open>
  open SpecCheck
  open SpecCheck_Generator
\<close>

(*
ranTypable(Max,R,X,V,Vs,N1,N2):-boltzmann_index(R),!,
  random(NewR),
  pickIndex(Max,NewR,X,Vs,V,N1,N2).
ranTypable(Max,R,l(A),(X->Xs),Vs,N1,N3):-boltzmann_lambda(R),!,
  next(Max,NewR,N1,N2),
  ranTypable(Max,NewR,A,Xs,[X|Vs],N2,N3).
ranTypable(Max,_R,a(A,B),Xs,Vs,N1,N5):-
  next(Max,R1,N1,N2),
  ranTypable(Max,R1,A,(X->Xs),Vs,N2,N3),
  next(Max,R2,N3,N4),
  ranTypable(Max,R2,B,X,Vs,N4,N5).

pickIndex(_,R,0,[V|_],V0,N,N):-boltzmann_leaf(R),!,
  unify_with_occurs_check(V0,V).
pickIndex(Max,_,s(X),[_|Vs],V,N1,N3):-
  next(Max,NewR,N1,N2),
  pickIndex(Max,NewR,X,Vs,V,N2,N3).
*)

ML \<open>
  (* Precomputed from the paper, presumably increasing the probability of
  boltzmann_index leads to smaller terms. Weaker effect when increasing the
  probability of boltzmann_lambda. *)
  fun boltzmann_index r = r < (* 0.1 *) 0.35700035696434995;
  fun boltzmann_lambda r = r < 0.6525813160382378;
  (* The probability p of de Bruijn index 0, generally Bound j has the
  probability (1-p)^j * p (geometric distribution) *)
  fun boltzmann_leaf r = r < (* 0.9 *) 0.7044190409261122;

  (* (rng state, env, maxidx) *)
  type term_state = SpecCheck_Random.rand * Type.tyenv * int;

  fun pick_index _ [] _ _ = error "pick_index: not below lambda"
    | pick_index (ctxt : Proof.context) (T::Ts) typ (s, env) =
    let
      val (r, s) = range_real (0.0, 1.0) s
    in
      if boltzmann_leaf r
        then
          (
            ((s, Sign.typ_unify (Proof_Context.theory_of ctxt) (T, typ) env), Bound 0)
            (* handle Type.TUNIFY => error ("pick_index: TUNIFY: " ^ Jeha_Common.pretty_typ ctxt T ^ "=" ^ Jeha_Common.pretty_typ ctxt typ ^ " in " ^ Jeha_Common.pretty_tyenv ctxt (fst env)) *)
          )
        else
          let val (state, Bound i) = pick_index ctxt Ts typ (s, env) in
            (state, Bound (i+1))
          end
    end;

  fun gen_tyvar ctxt maxidx =
    (maxidx + 1, TVar ((Name.aT, maxidx + 1), Sign.defaultS (Proof_Context.theory_of ctxt)));

  (* Generate a typable, closed random term. Rejection sampler with early abort
  that fails via exceptions. *)
  fun ran_typable
        (ctxt : Proof.context)
        (binder_types : typ list)
        (typ : typ)
        ((s, (typ_env, maxidx)) : SpecCheck_Random.rand * (Type.tyenv * int))
        : (SpecCheck_Random.rand * (Type.tyenv * int)) * term =
    let
      val (r, s) = range_real (0.0, 1.0) s
      (* val _ = writeln (@{make_string} r) *)
    in
      if boltzmann_index r
        then pick_index ctxt binder_types typ (s, (typ_env, maxidx))
      else if boltzmann_lambda r
        then
          let
            val (maxidx, arg_T) = gen_tyvar ctxt maxidx
            val (maxidx, return_T) = gen_tyvar ctxt maxidx
            (* The type of the thing we're generating. *)
            val lambda_typ = arg_T --> return_T
            (* The `typ` we were asked to return must unify the type we're
            actually generating *)
            val (typ_env, maxidx) =
              Sign.typ_unify
                (Proof_Context.theory_of ctxt)
                (lambda_typ, typ)
                (typ_env, maxidx)
            val (state, body) =
              ran_typable
                ctxt
                (arg_T :: binder_types)
                return_T
                (s, (typ_env, maxidx))
          in
            (state, Abs (Name.uu_, arg_T, body))
          end
      else
        let
          val (maxidx, arg_T) = gen_tyvar ctxt maxidx
          val (state, function) =
            ran_typable ctxt binder_types (arg_T --> typ) (s, (typ_env, maxidx))
          val (state, arg) =
            ran_typable ctxt binder_types arg_T state
        in
          (state, function $ arg)
        end
    end

  val boltzmann_term_gen : (term, SpecCheck_Random.rand) gen_state = fn s =>
    let
      val s = SpecCheck_Random.next s
      val (maxidx, T) = gen_tyvar @{context} ~1
      val ((s, (typ_env, maxidx)), t) =
        (ran_typable @{context} [] T (s, (Vartab.empty, maxidx))
           handle Type.TUNIFY => (writeln "TUNIFY" ; ((s, (Vartab.empty, maxidx)), Term.dummy))
        ) 
          handle (ERROR msg) =>
            (writeln ("ERROR: " ^ msg); ((s, (Vartab.empty, maxidx)), Term.dummy))
      val t =
        Envir.norm_term
          (Envir.Envir {maxidx = maxidx, tenv = Vartab.empty, tyenv = typ_env})
          t
    in
      (t, s)
    end
\<close>

declare [[speccheck_num_counterexamples = 1000]]
declare [[speccheck_max_success = 1000]]

ML \<open>
  val check_term = check (SpecCheck_Show.term @{context}) boltzmann_term_gen
  val _ = Lecker.test_group @{context} (SpecCheck_Random.new ()) [
    SpecCheck_Property.prop (K false) |> check_term "boltzmann generator"
  ]
\<close>

end
