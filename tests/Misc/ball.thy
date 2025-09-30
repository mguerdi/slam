theory ball

imports "HOL.Power" "SLAM.slam"

begin

(* Bounded universal quantification (Ball) *)

lemma eq_self_squared_imp_0_or_1:
  fixes n :: nat
  assumes "n = n\<^sup>2"
  shows "n = 0 \<or> n = 1"
  by (metis Suc_1 assms mult_eq_self_implies_10 power_Suc power_one_right)

lemma
  fixes A :: "nat set"
  assumes
    eq_squared: "\<forall>p \<in> A. p = p\<^sup>2"
  shows "\<forall>p \<in> A. p = 0 \<or> p = 1"
  (* using eq_self_squared_imp_0_or_1 eq_squared *)
  using eq_self_squared_imp_0_or_1 eq_squared
    (* by blast (* works *) *)
    (* by metis (* works *) *)
    (* using Ball_def by slam (* doesn't work (can't orient Ball_def correctly) *) *)
    (* FIXME: Check what the metis clausifier does to Ball *)
    (* FIXME: Try always unfolding Ball_def *)
    (* FIXME: Try custom outer clausification for Ball *)
    unfolding Ball_def by slam (* works *)

(* FIXME: similar things for Bex and If *)

end