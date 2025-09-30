theory exists_hoist

imports SLAM_TEST_BASE.test_base

begin

(* Based on forall_hoist.thy *)

ML \<open>
  val mkc = Thm.cterm_of @{context} 
\<close>

ML_val \<open>
  val premise = mkh @{prop "A \<Longrightarrow> B (\<exists>x. (f :: 'a \<Rightarrow> 'b \<Rightarrow> bool) x c) = B' \<Longrightarrow> D \<Longrightarrow> False"}
  val expected = mkh @{term_schem
    "A \<Longrightarrow> B True = B' \<Longrightarrow> D \<Longrightarrow> (f :: 'a \<Rightarrow> 'b \<Rightarrow> bool) ?fresh_x c \<noteq> False \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_exists_hoist
      @{context}
      { premise = premise
      , subterm = ([1], JLit.Left, 1)
      , fresh_x = mkc @{term_schem "?fresh_x :: 'a"}
      , predicate = @{cterm "\<lambda>x. (f :: 'a \<Rightarrow> 'b \<Rightarrow> bool) x c"} }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

(* Other schematic variables are present. *)
ML_val \<open>
  val premise = mkh @{term_schem "A ?y \<Longrightarrow> B (\<exists>x. (f :: 'a \<Rightarrow> 'b \<Rightarrow> bool) x c) = B' \<Longrightarrow> False"}
  val expected = mkh @{term_schem
    "A ?y \<Longrightarrow> B True = B' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b \<Rightarrow> bool) ?fresh_x c \<noteq> False \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_exists_hoist
      @{context}
      { premise = premise
      , subterm = ([1], JLit.Left, 1)
      , fresh_x = mkc @{term_schem "?fresh_x"}
      , predicate = @{cterm "\<lambda>x. (f :: 'a \<Rightarrow> 'b \<Rightarrow> bool) x c"} }
  val () = \<^assert> (eqh (expected, conclusion) )
\<close>

(* Expected failure if variable is not fresh. *)
ML_val \<open>
  val premise = mkh @{term_schem "A ?fresh_x \<Longrightarrow> B (\<exists>x. (f :: 'a \<Rightarrow> 'b \<Rightarrow> bool) x c) = B' \<Longrightarrow> False"}
  val expected = mkh @{term_schem
    "A \<Longrightarrow> B True = B' \<Longrightarrow> (f :: 'a \<Rightarrow> 'b \<Rightarrow> bool) ?fresh_x c \<noteq> False \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_exists_hoist
      @{context}
      { premise = premise
      , subterm = ([1], JLit.Left, 1)
      , fresh_x = @{cterm "fresh_x"}
      , predicate = @{cterm "\<lambda>x. (f :: 'a \<Rightarrow> 'b \<Rightarrow> bool) x c"} }
  val () = \<^assert> (not (eqh (expected, conclusion)))
\<close>

(* Type is also a schematic var. *)
ML_val \<open>
  val premise = mkh @{term_schem "B (\<exists>x. (f :: ?'a \<Rightarrow> 'b \<Rightarrow> bool) x c) = B' \<Longrightarrow> False"}
  val expected = mkh @{term_schem
    "B True = B' \<Longrightarrow> (f :: ?'a \<Rightarrow> 'b \<Rightarrow> bool) ?fresh_x c \<noteq> False \<Longrightarrow> False"}
  val conclusion =
    Slam_Proof.reconstruct_exists_hoist
      @{context}
      { premise = premise
      , subterm = ([1], JLit.Left, 0)
      , fresh_x = mkc @{term_schem "?fresh_x :: ?'a"}
      , predicate = Thm.cterm_of @{context} @{term_schem "\<lambda>x. (f :: ?'a \<Rightarrow> 'b \<Rightarrow> bool) x c"} }
  val () = \<^assert> (eqh (expected, conclusion))
\<close>

end