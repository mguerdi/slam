theory inj_pair

imports Main SLAM.slam

begin

lemma "inj (Pair a)" using [[metis_trace]] by (metis Pair_inject injI)

thm Pair_inject
thm injI

lemma "inj (Pair a)"
  (* either one does the trick *)
  (* using [[slam_sup_into_non_eligible]] *)
  using [[slam_sup_from_non_eligible]]
  (* by (slam Pair_inject injI[of "Pair a :: 'a \<Rightarrow> 'b \<times> 'a"]) *)
  by (slam Pair_inject injI)

end