theory fol_fitting_bug

imports HOL.Metis SLAM.slam

begin

lemma "\<forall>z. (\<lambda> x. z) = a"
  (* exception Fail raised (line 675 of "variable.ML"): Bad context: clash of fresh free for bound: :000 vs. xa *)
  (* using [[slam_meson]] by slam *)
  sorry

end