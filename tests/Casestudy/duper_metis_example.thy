theory duper_metis_example

imports SLAM.slam Main

begin

lemma "(\<Sum> i::nat=0..n. i) + (\<Sum> i::nat=0..n. i) = (\<Sum> i::nat=0..n. i + i)"
  (* sledgehammer[provers=zipperposition, dont_try0, instantiate=false]
  suggests:
    by (metis (no_types, lifting) ext sum.distrib) (6.7 s) 
    by (metis sum.distrib) (> 1.0 s, timed out) 
  *)
  (* sledgehammer[dont_try0]
  suggests:
    by (metis sum.distrib[of "\<lambda>uu. uu" "\<lambda>uu. uu"]) (13 ms) 
  and this
    by (smt (verit) sum.cong sum.distrib)
  which doesn't work.
  *)
  by (slam sum.distrib) (* 22 ms *)

end