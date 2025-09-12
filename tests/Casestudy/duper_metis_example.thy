theory duper_metis_example

imports SLAM.slam Main

begin

lemma "(\<Sum> i::nat=0..n. i) + (\<Sum> i::nat=0..n. i) = (\<Sum> i::nat=0..n. i + i)"
  sledgehammer[provers=zipperposition, dont_try0]
  (* by (metis sum.distrib[of "\<lambda>uu. uu" "\<lambda>uu. uu"]) (* 118 ms ? *) *)
  by (slam sum.distrib) (* 48 ms *)

end