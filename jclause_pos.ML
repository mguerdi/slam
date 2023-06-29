(* This should be in jclause.ML, but jeha_log.ML depends on cpos and full_pos, and jclause.ML
depends on jeha_log.ML so we need this file to break the cycle *)

signature JCLAUSE_POS =
sig
  (* position of literal in a clause *)
  type cpos = int
  type full_pos = JTerm.tpos * JLit.lpos * cpos
end;

structure JClause_Pos =
struct
  type cpos = int
  type full_pos = JTerm.tpos * JLit.lpos * cpos
end;