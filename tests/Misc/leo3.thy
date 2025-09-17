theory leo3

imports "SLAM.slam"

begin

(* Steen, Extensional Paramodulation for Higher-Order Logic and its Effective Implementation Leo-III
E2: Surjective Cantor Theorem.
      \<not>\<exists> fo\<iota>\<iota> . \<forall>Y o\<iota> . \<exists>X\<iota> . f X = Y
*)
lemma leo3_surjective_cantor_theorem:
  shows "\<not> (\<exists> f :: 'a \<Rightarrow> 'a \<Rightarrow> bool. \<forall> Y. \<exists> X. f X = Y)"
  (* sledgehammer *)
  (* suggested by sledgehammer but fails *)
  (* by metis *)
  (* using [[ slam_trace = false ]] by slam *)
  oops

end