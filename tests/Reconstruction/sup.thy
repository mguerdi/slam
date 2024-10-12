theory sup

imports JEHA_TEST_BASE.test_base

begin
  
ML \<open>
  (* Sup inference, left and right premise. *)
  val [DL1, DL2, DL3] = [@{term "DL1 :: bool"}, @{term "DL2 :: bool"}, @{term "DL3 :: bool"}]
  val t = @{term "t :: 'a"}
  val t' = @{term "t' :: 'a"}
  val t_eq_t' = HOLogic.mk_eq (t, t')
  val D = Skip_Proof.make_thm @{theory} (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [DL1, t_eq_t', DL2]), @{prop False}))
  (* val L = Skip_Proof.make_thm @{theory} @{prop "\<not> D \<Longrightarrow> (t' :: 'a) \<noteq> t \<Longrightarrow> False"} *)
  val C = Skip_Proof.make_thm @{theory} (@{prop "A t \<Longrightarrow> P (t :: 'a) \<noteq> Q \<Longrightarrow> \<not> B \<Longrightarrow> False :: bool"})
  val concl = Jeha_Proof.reconstruct_sup @{context} { left_premise=D, literal=(JLit.Left, 1), right_premise=C, subterm=([1], JLit.Left, 1) }
  val D2 = Skip_Proof.make_thm @{theory} (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [DL1, DL2, t_eq_t']), @{prop False}))
  val concl2 = Jeha_Proof.reconstruct_sup @{context} { left_premise=D2, literal=(JLit.Left, 2), right_premise=C, subterm=([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.prop_of concl aconv Thm.prop_of concl2)
  val D0 = Skip_Proof.make_thm @{theory} (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [t_eq_t', DL1, DL2]), @{prop False}))
  val concl0 = Jeha_Proof.reconstruct_sup @{context} { left_premise=D0, literal=(JLit.Left, 0), right_premise=C, subterm=([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.prop_of concl aconv Thm.prop_of concl0)
  val D_unit = Skip_Proof.make_thm @{theory} (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [t_eq_t']), @{prop False}))
  (* FIXME: assert something? *)
  val concl_unit = Jeha_Proof.reconstruct_sup @{context} {left_premise=D_unit, literal=(JLit.Left, 0), right_premise=C, subterm=([1], JLit.Left, 1) }
\<close>

(* Test other orientation *)

ML \<open>
  (* Sup inference, left and right premise. *)
  val [DL1, DL2, DL3] = [@{term "DL1 :: bool"}, @{term "DL2 :: bool"}, @{term "DL3 :: bool"}]
  val t = @{term "t :: 'a"}
  val t' = @{term "t' :: 'a"}
  val t_eq_t' = HOLogic.mk_eq (t, t')
  val D = Skip_Proof.make_thm @{theory} (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [DL1, t_eq_t', DL2]), @{prop False}))
  (* val L = Skip_Proof.make_thm @{theory} @{prop "\<not> D \<Longrightarrow> (t' :: 'a) \<noteq> t \<Longrightarrow> False"} *)
  val C = Skip_Proof.make_thm @{theory} (@{prop "A t \<Longrightarrow> P (t' :: 'a) \<noteq> Q \<Longrightarrow> \<not> B \<Longrightarrow> False :: bool"})
  val concl = Jeha_Proof.reconstruct_sup @{context} { left_premise=D, literal=(JLit.Right, 1), right_premise=C, subterm=([1], JLit.Left, 1) }
  val D2 = Skip_Proof.make_thm @{theory} (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [DL1, DL2, t_eq_t']), @{prop False}))
  val concl2 = Jeha_Proof.reconstruct_sup @{context} { left_premise=D2, literal=(JLit.Right, 2), right_premise=C, subterm=([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.prop_of concl aconv Thm.prop_of concl2)
  val D0 = Skip_Proof.make_thm @{theory} (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [t_eq_t', DL1, DL2]), @{prop False}))
  val concl0 = Jeha_Proof.reconstruct_sup @{context} { left_premise=D0, literal=(JLit.Right, 0), right_premise=C, subterm=([1], JLit.Left, 1) }
  val () = \<^assert> (Thm.prop_of concl aconv Thm.prop_of concl0)
  val D_unit = Skip_Proof.make_thm @{theory} (Logic.list_implies (map HOLogic.mk_Trueprop (map HOLogic.mk_not [t_eq_t']), @{prop False}))
  (* FIXME: assert something? *)
  val concl_unit = Jeha_Proof.reconstruct_sup @{context} {left_premise=D_unit, literal=(JLit.Right, 0), right_premise=C, subterm=([1], JLit.Left, 1) }
\<close>

end