theory preprocessing

imports "SLAM_TEST_BASE.test_base"

begin

(* from: HOL/ex/SAT_Examples.thy *)

(* FIXME *)
lemma "(\<forall>x. P x) \<or> \<not> All P"
by slam

end
