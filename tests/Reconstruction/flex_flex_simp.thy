theory flex_flex_simp

imports SLAM_TEST_BASE.test_base

begin

ML \<open>
  val empty = mkh @{prop "False"}
\<close>

ML_val \<open>
  val c = mkh @{term_schem "?a = ?b \<Longrightarrow> False"}
  val c' = Slam_Proof.reconstruct_flex_flex_simp @{context} { premise = c }
\<close>

ML_val \<open>
  val c = mkh @{term_schem "?a c = ?b d \<Longrightarrow> False"}
  val c' = Slam_Proof.reconstruct_flex_flex_simp @{context} { premise = c }
  val () = \<^assert> (eqh (c', empty))
\<close>

ML_val \<open>
  val c = mkh @{term_schem "?a = ?b \<Longrightarrow> ?a = ?b \<Longrightarrow> False"}
  val c' = Slam_Proof.reconstruct_flex_flex_simp @{context} { premise = c }
  val () = \<^assert> (eqh (c', empty))
\<close>

ML_val \<open>
  val c = mkh @{term_schem "?a = ?b \<Longrightarrow> ?a = ?c \<Longrightarrow> False"}
  val c' = Slam_Proof.reconstruct_flex_flex_simp @{context} { premise = c }
  val () = \<^assert> (eqh (c', empty))
\<close>

ML_val \<open>
  val c = mkh @{term_schem "?a a = ?b b \<Longrightarrow> ?a c = ?c d \<Longrightarrow> False"}
  val c' = Slam_Proof.reconstruct_flex_flex_simp @{context} { premise = c }
  val () = \<^assert> (eqh (c', empty))
\<close>

ML_val \<open>
  val c = mkh @{term_schem "?a a b = ?a b c \<Longrightarrow> ?a (d ?a) = ?a e \<Longrightarrow> False"}
  val c' = Slam_Proof.reconstruct_flex_flex_simp @{context} { premise = c }
  val () = \<^assert> (eqh (c', empty))
\<close>

ML_val \<open>
  val c: HClause.hthm =
    { th = mk @{term_schem "sk = sk_def \<Longrightarrow> ?a = ?b \<Longrightarrow> False"}
    , skolems = [(@{term "sk"}, @{term "sk_def"})]
    }
  val c' = Slam_Proof.reconstruct_flex_flex_simp @{context} { premise = c }
  val () = \<^assert> (eqh (c', empty))
\<close>

ML_val \<open>
  val c = mkh @{term_schem "?x a \<noteq> ?y b \<Longrightarrow> False"}
  val () = \<^assert_cant>\<open>Slam_Proof.reconstruct_flex_flex_simp @{context} { premise = c }\<close>
\<close>

end
