theory subsumption

imports "SLAM.slam" HOL.HOL

begin

declare [[slam_trace]]

setup \<open>Slam_Common.term_pat_setup\<close>
setup \<open>Slam_Common.type_pat_setup\<close>

(* no unification *)
ML_val \<open>
  val subset = JClause.of_term @{context} (@{term_pat "x = y"}, 0);
  val superset = JClause.of_term @{context} (@{term_pat "x = y \<or> v = w"}, 1);
  \<^assert> (Slam_Subsumption.subsumes (Context.Proof @{context}) (subset, superset))
\<close>

(* multiset subsumption *)
ML_val \<open>
  val not_sub_multiset = JClause.of_term @{context} (@{term_pat "x = y \<or> x = y"}, 0);
  val superset = JClause.of_term @{context} (@{term_pat "x = y \<or> v = w"}, 1);
  \<^assert> (not
    (Slam_Subsumption.subsumes (Context.Proof @{context}) (not_sub_multiset, superset))
  )
\<close>

(* simple unification *)
ML_val \<open>
  val sub_generalization = JClause.of_term @{context} (@{term_pat "f ?x = g ?x"}, 0);
  val superset = JClause.of_term @{context} (@{term_pat "f c = g c \<or> False"}, 1);
  \<^assert> (Slam_Subsumption.subsumes (Context.Proof @{context}) (sub_generalization, superset))
\<close>

(* unordered literals *)
ML_val \<open>
  val unit = JClause.of_term @{context} (@{term_pat "c = d"}, 0);
  val flipped_unit = JClause.of_term @{context} (@{term_pat "d = c"}, 1);
  \<^assert> (Slam_Subsumption.subsumes (Context.Proof @{context}) (unit, flipped_unit))
\<close>

(* backtracking *)
ML_val \<open>
  (* first attempts ?y := c but only ?y := d works *)
  val c = JClause.of_term @{context} (@{term_pat "c = ?y \<or> c = c"}, 0);
  val d = JClause.of_term @{context} (@{term_pat "c = c \<or> False \<or> d = c"}, 1);
  \<^assert> (Slam_Subsumption.subsumes (Context.Proof @{context}) (c, d))
\<close>

(* no matcher *)
ML_val \<open>
  val c = JClause.of_term @{context} (@{term_pat "c = ?y \<or> d = ?y"}, 0);
  val d = JClause.of_term @{context} (@{term_pat "c = e \<or> d = f"}, 1);
  \<^assert> (not
    (Slam_Subsumption.subsumes (Context.Proof @{context}) (c, d))
  )
\<close>

(* higher-order matcher *)
ML_val \<open>
  val c = JClause.of_term @{context} (@{term_pat "(?f :: bool \<Rightarrow> bool) c"}, 0);
  val d = JClause.of_term @{context} (@{term_pat "c :: bool"}, 1);
  \<^assert> (Slam_Subsumption.subsumes (Context.Proof @{context}) (c, d))
\<close>

end
