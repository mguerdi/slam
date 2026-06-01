chapter SLAM

session "SLAM" = "HOL-TPTP" +
  description "
    an implementation of lambda-superposition with booleans
  "
  theories
    slam_base
    slam_lemma
    slam_tactic
    slam
    (* slam_sledgehammer *)
    (* slam_debug *)

session "SLAM_MIRABELLE" in Mirabelle = SLAM +
  description "
    mirabelle action for running slam
  "
  theories
    Mirabelle_Slam

session "SLAM_TPTP" in slam_tptp = SLAM +
  description "
    slam for tptp problems
  "
  theories
    slam_tptp
