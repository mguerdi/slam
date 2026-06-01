theory ALG023_plus_1

imports "SLAM_TPTP.slam_tptp"

begin

(* declare [[slam_trace]] *)
(* declare [[slam_delayed_unification=false]] *)
(* declare [[slam_debug_trace_all_clauses]] *)
(* declare [[slam_literal_selection_function="select_none"]] *)
(* declare [[slam_trace_sup]] *)

declare [[slam_trace_passive=false]]
declare [[slam_trace_active=false]]
declare [[slam_max_number_of_steps=100000]]

declare [[slam_disable_all]]
(* declare [[slam_rule_sup]] *)
declare [[slam_rule_bool_simp]]
declare [[slam_rule_simp_outer_claus]]
declare [[slam_rule_e_res]]
declare [[slam_rule_sup]]

(* just combinatorics? *)
ML \<open> Slam_ATP_Problem_Import.slam_tptp_file @{theory} (10) "/home/massin/research/tptp/TPTP-v9.0.0/Problems/ALG/ALG023+1.p" \<close>

(*
One Problem:

Sup:
  bnd_greater_than_0 (?X::TPTP_Interpret.ind) = False \<or>
  \<langle><\<lblot>bnd_product ?X                          ?X                          bnd_additive_identity \<approx>~-> False\<rblot>>\<rangle>
into
  \<langle><\<lblot>bnd_product bnd_multiplicative_identity bnd_multiplicative_identity bnd_additive_identity\<rblot>>\<rangle> = False

Sup:
   bnd_product (?X::TPTP_Interpret.ind)    ?X                          bnd_additive_identity
=\<^sup>? bnd_product bnd_multiplicative_identity bnd_multiplicative_identity bnd_additive_identity

Sup: fail: u not eligible in

\<langle><\<lblot>bnd_product bnd_multiplicative_identity bnd_multiplicative_identity bnd_additive_identity\<rblot>>\<rangle> = False
*)

end
