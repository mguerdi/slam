theory fast_kbo 

imports JEHA_TEST_BASE.test_base 

begin


ML_val \<open>
  infix 6 >!
  infix 6 <!
  infix 6 =!
  infix 6 <!>
  fun s >! t = Jeha_KBO.T_tckbo Jeha_KBO.empty s t
  fun s <! t = Jeha_KBO.T_tckbo Jeha_KBO.empty t s
  val a = @{typ_pat "?'a"}
  val b = @{typ_pat "?'b"}
  val T = @{typ "'c"}
  val T' = @{typ "'d"}
  val (_, SOME EQUAL) = T >! T 
  val (_, res') = Jeha_KBO.T_tckbo Jeha_KBO.empty T T'
  val (_, res'') = Jeha_KBO.T_tckbo Jeha_KBO.empty T' T
  val (_, res''') = Jeha_KBO.T_tckbo Jeha_KBO.empty a a
  val (_, res'''') = Jeha_KBO.T_tckbo Jeha_KBO.empty T a
  val (_, res''''') = Jeha_KBO.T_tckbo Jeha_KBO.empty a T
  val fT = @{typ_pat "?'a \<Rightarrow> 'c"}
  val (_, res'''''') = Jeha_KBO.T_tckbo Jeha_KBO.empty fT fT
  val (_, res''''''') = Jeha_KBO.T_tckbo Jeha_KBO.empty fT a
  val (_, res'''''''') = Jeha_KBO.T_tckbo Jeha_KBO.empty a fT
  val (_, res''''''''') = Jeha_KBO.T_tckbo Jeha_KBO.empty b fT 
  val fT' = @{typ_pat "?'a \<Rightarrow> ?'b"}
  val (_, res'''''''''') = Jeha_KBO.T_tckbo Jeha_KBO.empty fT fT'
  val (_, res''''''''''') = Jeha_KBO.T_tckbo Jeha_KBO.empty fT' fT
\<close>

ML_val \<open>
  val s = @{term "a :: 'a"}
  val t = @{term "b :: 'a"}
  val res1 = Jeha_KBO.ord (s, s) 
  val res2 = Jeha_KBO.ord (s, t)
  val res3 = Jeha_KBO.ord (t, s) 
  val x = @{term_schem "?x :: 'a"}
  val y = @{term_schem "?y :: 'a"}
  val res4 = Jeha_KBO.ord (x, x)
  val res5 = Jeha_KBO.ord (x, y)
  val f_x = @{term_schem "f (?x :: 'a)"}
  val res6 = Jeha_KBO.ord (f_x, f_x)
  val res7 = Jeha_KBO.ord (f_x, x)
  val res8 = Jeha_KBO.ord (x, f_x)
  val l_x = @{term_schem "\<lambda>y :: 'b. ?x :: 'a"}
  val res9 = Jeha_KBO.ord (l_x, x)
\<close>


end