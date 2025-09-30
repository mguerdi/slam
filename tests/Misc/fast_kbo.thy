theory fast_kbo 

imports SLAM_TEST_BASE.test_base 

begin

ML_val \<open>
  infix 6 >!
  infix 6 <!
  infix 6 =!
  infix 6 <!>
  fun s >! t =
    (\<^assert> (SOME GREATER = #2 (Slam_KBO.T_tckbo Slam_KBO.empty s t));
    \<^assert> (SOME LESS = #2 (Slam_KBO.T_tckbo Slam_KBO.empty t s)))
  fun s <! t = t >! s 
  fun s =! t =
    (\<^assert> (SOME EQUAL = #2 (Slam_KBO.T_tckbo Slam_KBO.empty s t));
    \<^assert> (SOME EQUAL = #2 (Slam_KBO.T_tckbo Slam_KBO.empty t s)))
  fun s <!> t = 
    (\<^assert> (NONE = #2 (Slam_KBO.T_tckbo Slam_KBO.empty s t));
    \<^assert> (NONE = #2 (Slam_KBO.T_tckbo Slam_KBO.empty t s)))

  val a = @{typ_pat "?'a"}
  val b = @{typ_pat "?'b"}
  val T = @{typ "'c"}
  val T' = @{typ "'d"}
  val () = T =! T
  val () = T' >! T
  val () = a =! a
  val () = T <!> a
  val fT = @{typ_pat "?'a \<Rightarrow> 'c"}
  val () = fT =! fT
  val () = fT >! a
  val () = b <!> fT 
  val fT' = @{typ_pat "?'a \<Rightarrow> ?'b"}
  val () = fT <!> fT'
\<close>

ML_val \<open>
  infix 6 >!
  infix 6 <!
  infix 6 =!
  infix 6 <!>
  fun s >! t =
    (\<^assert> (SOME GREATER = Slam_KBO.ord (s, t));
    \<^assert> (SOME LESS = Slam_KBO.ord (t, s)))
  fun s <! t = t >! s 
  fun s =! t =
    (\<^assert> (SOME EQUAL = Slam_KBO.ord (s, t));
    \<^assert> (SOME EQUAL = Slam_KBO.ord (t, s))) 
  fun s <!> t = 
    (\<^assert> (NONE = Slam_KBO.ord (s, t)); 
    \<^assert> (NONE = Slam_KBO.ord (t, s))) 

  val s = @{term "a :: 'a"}
  val t = @{term "b :: 'a"}
  val () = s =! s 
  val () = s <! t
  val x = @{term_schem "?x :: 'a"}
  val y = @{term_schem "?y :: 'a"}
  val () = x =! x 
  val () = x <!> y 
  val f_x = @{term_schem "f (?x :: 'a)"}
  val () = f_x =! f_x
  val () = f_x >! x
  val l_x = @{term_schem "\<lambda>y :: 'b. ?x :: 'a"}
  val () = l_x <!> x
\<close>

ML_val \<open>
  infix 6 >!
  infix 6 <!
  infix 6 =!
  infix 6 <!>
  fun s >! t =
    (\<^assert> (SOME GREATER = JLit.kbo (s, t));
    \<^assert> (SOME LESS = JLit.kbo (t, s)))
  fun s <! t = t >! s 
  fun s =! t =
    (\<^assert> (SOME EQUAL = JLit.kbo (s, t));
    \<^assert> (SOME EQUAL = JLit.kbo (t, s))) 
  fun s <!> t = 
    (\<^assert> (NONE = JLit.kbo (s, t)); 
    \<^assert> (NONE = JLit.kbo (t, s))) 

  val n = JLit.norm_negative_pred @{context}

  val t_neq_t = JLit.of_term @{term "True \<noteq> True"}
  val t_neq_f = JLit.of_term @{term "True \<noteq> False"}
  val f_neq_t = JLit.of_term @{term "False \<noteq> True"}
  val f_neq_f = JLit.of_term @{term "False \<noteq> False"}
  val () = t_neq_t =! n t_neq_t
  val () = t_neq_f >! n t_neq_f
  val () = f_neq_t >! n f_neq_t
  val () = f_neq_f >! n f_neq_f

  val x_neq_f = JLit.of_term @{term_schem "?x \<noteq> False"}
  val x_neq_t = JLit.of_term @{term_schem "?x \<noteq> True"}
  val () = x_neq_f >! n x_neq_f
  val () = x_neq_t =! n x_neq_t
\<close>

ML_val \<open>
  val c = JClause.of_term @{context} (@{term "a \<noteq> (b :: bool)"}, 0)
  val c' = Slam_Proof_Util.norm_negative_predicate_literals @{context} (Skip_Proof.make_thm @{theory} (HOLogic.mk_Trueprop (JClause.term_of c)))
\<close>

ML_val \<open>
  val c = JClause.of_term @{context} (@{term_schem "?x a = False \<or> ?x b = True"}, 0)
  val b = JClause.is_eligible_cpos c 0
  val b' = JClause.is_eligible_cpos c 1
  val c' = JClause.of_term @{context} (@{term "True = False \<or> True = True"}, 1)
  val b'' = JClause.is_eligible_cpos c' 0
  val b''' = JClause.is_eligible_cpos c' 1
  val [d] = Slam.infer_false_elim @{context} c (JLit.Right, 0)
\<close>

end