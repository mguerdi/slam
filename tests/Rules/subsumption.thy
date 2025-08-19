theory subsumption

imports JEHA_TEST_BASE.test_base HOL.List

begin

declare [[jeha_trace]]
declare [[jeha_disable_all]]
declare [[jeha_rule_clause_subsumption]]
declare [[jeha_trace_forward_simp]]
declare [[jeha_trace_backward_simp]]
declare [[jeha_trace_clause_subsumption]]

ML \<open>
  val c = JClause.of_term @{context} (@{term "a \<or> b"}, 0)
  val d = JClause.of_term @{context} (@{term_schem "?x \<or> b"}, 1)
  val () = writeln (Jeha_Common.pretty_terms @{context} (map JClause.term_of [c, d]))
  val symbols = Subsumption_Index.collect_symbols [c, d] 
  val index =
    Subsumption_Index.make_index symbols
    |> Subsumption_Index.insert_clause d
  val () = \<^assert> ([1] = Subsumption_Index.fold_subsuming c (curry op::) index [])
\<close>

ML \<open>
  val c = JClause.of_term @{context} (@{term "a \<or> b"}, 0)
  val d = JClause.of_term @{context} (@{term_schem "?x \<or> b"}, 1)
  val () = writeln (Jeha_Common.pretty_terms @{context} (map JClause.term_of [c, d]))
  val symbols = Subsumption_Index.collect_symbols [c, d] 
  val index =
    Subsumption_Index.make_index symbols
    |> Subsumption_Index.insert_clause c
  val () = \<^assert> ([] = Subsumption_Index.fold_subsuming d (curry op::) index [])
\<close>

lemma "(\<And>x. f x) \<Longrightarrow> f a \<or> False \<Longrightarrow> f b"
  using [[jeha_rule_forall_hoist, jeha_rule_simp_false_elim]] by jeha

ML_val \<open>
  (* potentially subsuming clause *)
  val ct = @{term_schem
    "map (?f::bool \<Rightarrow> ?'b) (?xs::bool list) = map (?g::bool \<Rightarrow> ?'b) ?xs
    \<or> (False \<in> set ?xs) = True
    \<or> (True \<in> set ?xs) = True"
  }
  (* potentially subsumed clause *)
  val dt = @{term_schem
    "(False \<in> set (?xs::bool list)) = True
    \<or> (True \<in> set ?xs) = True
    \<or> map (?g6::bool \<Rightarrow> ?'b) ?xs = map (?g::bool \<Rightarrow> ?'b) ?xs"
  }
  val c = JClause.of_term @{context} (ct, 0)
  val d = JClause.of_term @{context} (dt, 1)
  val r = Jeha_Subsumption.subsumes (Context.Proof @{context}) (c, d)
\<close>

(* From simple_stuff.thy
  theorem T0: "\<exists>F. \<forall>T :: bool. \<exists>(S :: bool\<Rightarrow>bool). F S = T" ... by jeha

output:
(CS) :forward subsumption of 13918:jsk116__ (\<lambda>a. jsk116__ ?x_oc4) = True \<or> ?x_oc4 ?x_oc5 \<noteq> True (SimpFalseElim [13827]) 
(CS) :fail: not subsumed by 12847:jsk116__ (\<lambda>a. jsk116__ ?x_oc2) = True \<or> ?x_oc2 ?x_oc3 \<noteq> True (SimpFalseElim [12762]) 
*)
(* doesn't work with this type *)
ML_val \<open>
  val ct = @{term_schem "jsk116 (\<lambda>a. jsk116 (?x_oc2 :: (bool \<Rightarrow> bool) \<Rightarrow> bool)) = True \<or> ?x_oc2 ?x_oc3 \<noteq> True"}
  val dt = @{term_schem "jsk116 (\<lambda>a. jsk116 (?x_oc4 :: (bool \<Rightarrow> bool) \<Rightarrow> bool)) = True \<or> ?x_oc4 ?x_oc5 \<noteq> True"}
  val c = JClause.of_term @{context} (ct, 0)
  val d = JClause.of_term @{context} (dt, 1)
  val r = Jeha_Subsumption.subsumes (Context.Proof @{context}) (c, d)
  val () = \<^assert> r
\<close>

(* doesn't but does work with this type *)
ML_val \<open>
  val ct = @{term_schem "jsk116 (\<lambda>a. jsk116 (?x_oc2 :: 'b \<Rightarrow> bool)) = True \<or> ?x_oc2 ?x_oc3 \<noteq> True"}
  val dt = @{term_schem "jsk116 (\<lambda>a. jsk116 (?x_oc4 :: 'b \<Rightarrow> bool)) = True \<or> ?x_oc4 ?x_oc5 \<noteq> True"}
  val c = JClause.of_term @{context} (ct, 0)
  val d = JClause.of_term @{context} (dt, 1)
  val r = Jeha_Subsumption.subsumes (Context.Proof @{context}) (c, d)
  val () = \<^assert> r
\<close>

(* Reason seems to be the solution to this unification problem *)

(*
declare [[unify_trace]]
declare [[unify_trace, unify_trace_simp, unify_trace_failure, unify_trace_bound=0]]
*)

ML_val \<open>
  val ct = @{term_schem "(?E :: (bool \<Rightarrow> bool) \<Rightarrow> bool) ?f"}
  val dt = @{term_schem "(G :: (bool \<Rightarrow> bool) \<Rightarrow> bool) h"}
  (* *)
  val SOME (matcher1, matchers) =
    Unify.matchers (Context.Proof @{context}) [(ct, dt)]
    |> Seq.pull
  val () = writeln ("matcher1: " ^ Jeha_Common.pretty_tenv @{context} (Envir.term_env matcher1))
(*
  ?E := \<lambda>a. a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (a (G h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  ?f := \<lambda>a. a
  so ?E ?f becomes G h
*)
(*
  val (matchers, _) = Seq.chop 1000 matchers
  fun write_matcher (i: int, matcher) =
    writeln ("matcher" ^ @{make_string} i ^ ": " ^ Jeha_Common.pretty_tenv @{context} (Envir.term_env matcher))
  val _ = map_index write_matcher matchers
*)
\<close>

ML_val \<open>
  val ct = @{term_schem "(?E :: (bool \<Rightarrow> bool) \<Rightarrow> bool) ?f"}
  val dt = @{term_schem "(G :: (bool \<Rightarrow> bool) \<Rightarrow> bool) h"}
  (* *)
  val SOME (matcher1, matchers) =
    Unify.matchers (Context.Proof @{context}) [(ct, dt)]
    |> Seq.pull
  val () = writeln ("matcher1: " ^ Jeha_Common.pretty_tenv @{context} (Envir.term_env matcher1))
\<close>

(* whereas here it's normal *)
ML_val \<open>
  val ct = @{term_schem "?E ?f"}
  val dt = @{term_schem "G h"}
  val matcher =
    Jeha_Unify.matchers (Context.Proof @{context}) 10 [(ct, dt)]
    |> Seq.hd
  val () = writeln (Jeha_Common.pretty_tenv @{context} (Envir.term_env matcher))
(*
  ?E := G,
  ?f := h
  so ?E ?f becomes G h
*)
\<close>

end
