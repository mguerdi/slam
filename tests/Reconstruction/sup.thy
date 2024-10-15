theory sup

imports JEHA_TEST_BASE.test_base

begin

ML \<open>
  val mk = Skip_Proof.make_thm @{theory}
\<close>


ML_val \<open>
  (* Sup inference, left and right premise. *)
  val [DL1, DL2, DL3] = [@{term "DL1 :: bool"}, @{term "DL2 :: bool"}, @{term "DL3 :: bool"}]
  val t = @{term "t :: 'a"}
  val t' = @{term "t' :: 'a"}
  val t_eq_t' = HOLogic.mk_eq (t, t')
  val D = mk (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [DL1, t_eq_t', DL2]), @{prop False}))
  (* val L = Skip_Proof.make_thm @{theory} @{prop "\<not> D \<Longrightarrow> (t' :: 'a) \<noteq> t \<Longrightarrow> False"} *)
  val C = mk (@{prop "A (t :: 'a) \<Longrightarrow> P (t :: 'a) \<noteq> (Q :: 'b) \<Longrightarrow> \<not> B \<Longrightarrow> False :: bool"})
  val concl = Jeha_Proof.reconstruct_sup @{context} { left_premise=D, literal=(JLit.Left, 1), right_premise=C, subterm=([1], JLit.Left, 1) }
  val D2 = mk (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [DL1, DL2, t_eq_t']), @{prop False}))
  val concl2 = Jeha_Proof.reconstruct_sup @{context} { left_premise=D2, literal=(JLit.Left, 2), right_premise=C, subterm=([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.prop_of concl aconv Thm.prop_of concl2)
  val D0 = mk (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [t_eq_t', DL1, DL2]), @{prop False}))
  val concl0 = Jeha_Proof.reconstruct_sup @{context} { left_premise=D0, literal=(JLit.Left, 0), right_premise=C, subterm=([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.prop_of concl aconv Thm.prop_of concl0)
  val D_unit = mk (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [t_eq_t']), @{prop False}))
  val concl_unit = Jeha_Proof.reconstruct_sup @{context} {left_premise=D_unit, literal=(JLit.Left, 0), right_premise=C, subterm=([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.eq_thm (concl_unit, mk @{prop "A (t :: 'a) \<Longrightarrow> P (t' :: 'a) \<noteq> (Q :: 'b) \<Longrightarrow> \<not>B \<Longrightarrow> False"}))
\<close>

(* Test other orientation *)
ML_val \<open>
  (* Sup inference, left and right premise. *)
  val [DL1, DL2, DL3] = [@{term "DL1 :: bool"}, @{term "DL2 :: bool"}, @{term "DL3 :: bool"}]
  val t = @{term "t :: 'a"}
  val t' = @{term "t' :: 'a"}
  val t_eq_t' = HOLogic.mk_eq (t, t')
  val D = mk (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [DL1, t_eq_t', DL2]), @{prop False}))
  (* val L = mk @{prop "\<not> D \<Longrightarrow> (t' :: 'a) \<noteq> t \<Longrightarrow> False"} *)
  val C = mk (@{prop "A (t :: 'a) \<Longrightarrow> P (t' :: 'a) \<noteq> (Q :: 'b) \<Longrightarrow> \<not> B \<Longrightarrow> False :: bool"})
  val concl = Jeha_Proof.reconstruct_sup @{context} { left_premise=D, literal=(JLit.Right, 1), right_premise=C, subterm=([1], JLit.Left, 1) }
  val D2 = mk (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [DL1, DL2, t_eq_t']), @{prop False}))
  val concl2 = Jeha_Proof.reconstruct_sup @{context} { left_premise=D2, literal=(JLit.Right, 2), right_premise=C, subterm=([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.prop_of concl aconv Thm.prop_of concl2)
  val D0 = mk (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [t_eq_t', DL1, DL2]), @{prop False}))
  val concl0 = Jeha_Proof.reconstruct_sup @{context} { left_premise=D0, literal=(JLit.Right, 0), right_premise=C, subterm=([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.prop_of concl aconv Thm.prop_of concl0)
  val D_unit = mk (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [t_eq_t']), @{prop False}))
  val concl_unit = Jeha_Proof.reconstruct_sup @{context} {left_premise=D_unit, literal=(JLit.Right, 0), right_premise=C, subterm=([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.eq_thm (concl_unit, mk @{prop "A (t :: 'a) \<Longrightarrow> P (t :: 'a) \<noteq> (Q :: 'b) \<Longrightarrow> \<not>B \<Longrightarrow> False"}))
\<close>

(* In the presence of schematic vars. *)
ML_val \<open>
  val right_premise = mk @{term_schem "A \<Longrightarrow> B (?x :: 'a) (t :: 'b) \<noteq> (B' :: ?'c) \<Longrightarrow> False"}
  val left_premise = mk @{term_schem "(t :: 'b) \<noteq> C (?y :: ?'d) \<Longrightarrow> False"}
  val expected = mk @{term_schem "A \<Longrightarrow> B (?x :: 'a) (C (?y :: ?'d)) \<noteq> (B' :: ?'c) \<Longrightarrow> False"}
  val conclusion =
    Jeha_Proof.reconstruct_sup
      @{context}
      { left_premise = left_premise
      , literal = (JLit.Left, 0)
      , right_premise = right_premise
      , subterm = ([2], JLit.Left, 1) }
  val () = \<^assert> (Thm.eq_thm (conclusion, expected))
\<close>

end