theory Selectivities

imports SLAM_TEST_BASE.test_base Main

begin

(* declare [[show_types, show_sorts]] *)
declare [[show_types]]

(* consts foldl :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" *)

(*
datatype (set: 'a) mylist =
    MyNil  (\<open>[]\<close>)
  | MyCons (hd: 'a) (tl: "'a mylist")

consts foldl :: "('d \<Rightarrow> 'b \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'b mylist \<Rightarrow> 'd"
consts foldr :: "('b \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> 'b mylist \<Rightarrow> 'd \<Rightarrow> 'd"
*)
consts one :: 'a
consts mytimes :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

(*
lemma a1: "\<And>f x y. list_sel f x y = foldl (\<lambda>a b. mytimes a (list_sel_aux f b y)) one x"
  sorry

lemma a2: "\<And>f x y. foldl (\<lambda>a b. mytimes a (f x b)) one y = foldr (\<lambda>b a. mytimes a (f x b)) y one"
  sorry
*)

(* The issue I was having:
Unspecified type vars in "assume"d statements are all fresh TFrees, and can't be instantiated when
using the assumptions. *)

lemma "mocked_list_sel_eq_fold":
  fixes list_sel_aux :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd"
  (* fixes foldl
  fixes foldr *)
  (* fixes foldl :: "('d::{one,times} \<Rightarrow> 'b::type \<Rightarrow> 'd::{one,times}) \<Rightarrow> 'd::{one,times} \<Rightarrow> 'b::type list \<Rightarrow> 'd::{one,times}" *)
  assumes
    (* list_sel is a foldl of list_sel_aux ... *)
    a1: "\<And>f x y. list_sel f x y = foldl (\<lambda>a b. mytimes a (list_sel_aux f b y)) one x"
    (* foldl and foldr agree (f := list_sel_aux) *)
    and a2: "\<And>f x y. foldl (\<lambda>(a :: 'd) (b :: 'b). mytimes a (f x b)) one y = foldr (\<lambda>b a. mytimes a (f x b)) y one"
    (* list_sel is a foldr of list_sel_aux *)
  shows "list_sel f x y = foldr (\<lambda>b a. mytimes a (list_sel_aux f b y)) x one"
  (* manual proof *)
  unfolding a1
  (* using a2[of "\<lambda>z_x z_b. list_sel_aux f z_b y"] *)
  apply (rule a2[of "\<lambda>z_x z_b. list_sel_aux f z_b y"])
  (* apply (rule a2[of "\<lambda>z_x z_b. list_sel_aux f z_b y"]) *)
  done

  (* sledgehammer *)
  (* using a2[of "\<lambda>v b. list_sel_aux f b v"] *)
  (* using assms [[slam_trace]] by slam *)

consts list_sel_aux :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd"
consts list_sel :: "'a \<Rightarrow> 'b list \<Rightarrow> 'c \<Rightarrow> 'd"

lemma "properly_mocked_list_sel_eq_fold":
  fixes bla :: "'d :: {one, times}"
  fixes f :: "'a"
  fixes x :: "'b list"
  fixes y :: 'c
  assumes
    a1: "\<And>(f :: 'a) (bs :: 'b list) (y :: 'c).
      list_sel f bs y = foldl (\<lambda>(a :: 'd) b. a * (list_sel_aux f b y)) 1 bs" and
    a2: "\<And>f x (bs :: 'b list).
      foldl (\<lambda>(a :: 'd) (b :: 'b). a * (f x b)) 1 bs = foldr (\<lambda>b a. a * (f x b)) bs 1"
  shows "list_sel f x y = foldr (\<lambda>b (a :: 'd). a * (list_sel_aux f b y)) x 1"
  unfolding a1
  apply (rule a2)

  (* apply (rule a2[of "\<lambda>z_x z_b. list_sel_aux f z_b y"]) *)
  sorry
  
lemma "reduced_list_sel_eq_fold":
  fixes bla :: "'d :: {one, times}"
  fixes f :: "'a"
  fixes x :: "'b list"
  fixes y :: 'c
  assumes
    a1: "\<And>(f :: 'a) (bs :: 'b list) (y :: 'c).
      list_sel f bs y = foldl (\<lambda>(a :: 'd) b. a * (list_sel_aux f b y)) 1 bs" and
    (* Note: Without the "x", metis is able to prove it. *)
    a2: "\<And>f x (bs :: 'b list).
      foldl (\<lambda>(acc :: 'd) (b :: 'b). acc * f x b) 1 bs = foldr (\<lambda>b acc. acc * f x b) bs 1"
  shows "list_sel f x y = foldr (\<lambda>b (a :: 'd). a * (list_sel_aux f b y)) x 1"
  (*
  unfolding a1
  apply (rule a2)
  *)
  (* sledgehammer *)
  (* by (metis a1 a2) *)
  (* by (slam a1 a2) *)

  (* apply (rule a2[of "\<lambda>z_x z_b. list_sel_aux f z_b y"]) *)
  sorry

(*
lemma list_sel_and_aux: "list_sel f bs y = foldl (\<lambda>a b. a * (list_sel_aux f b y)) 1 bs"
  sorry

lemma foldl_foldr:
  "foldl (\<lambda>acc b. acc * f x b) 1 bs = foldr (\<lambda>b acc. acc * f x b) bs 1"
  sorry
*)

lemma list_sel_eq_foldl: "list_sel f x y = foldl (\<lambda>a b. a * list_sel_aux f b y) 1 x"
  sorry

(* the type annotation on x is what make metis fail *)
lemma sel_foldl_eq_foldr:
  "foldl (\<lambda>a (b :: 'b). a * f (x :: 'b) b) 1 y = foldr (\<lambda>b a. a * f x b) y 1"
  sorry

lemma list_sel_eq_fol:
  "list_sel f x y = foldr (\<lambda>b a. a * (list_sel_aux f b y)) x 1"
  (* unfolding list_sel_and_aux
  by (rule foldl_foldr) *)
  (* sledgehammer *)
  (* by (metis foldl_foldr list_sel_and_aux) *)
  (* by (metis list_sel_eq_foldl sel_foldl_eq_foldr) *)
  using [[slam_trace]] by (slam list_sel_eq_foldl sel_foldl_eq_foldr)

(* thm mocked_list_sel_eq_fold[where foldr=foldr] *)

(*
lemma "mocked_list_sel_eq_fold":
  assumes
    (* list_sel is a foldl of list_sel_aux ... *)
    "\<And>f x y. list_sel f x y = foldl (\<lambda>a b. a * list_sel_aux f b y) 1 x"
    (* foldl and foldr agree (f := list_sel_aux) *)
    and "\<And>f x y. foldl (\<lambda>a b. a * f x b) 1 y = foldr (\<lambda>b a. a * f x b) y 1"
    (* list_sel is a foldr of list_sel_aux *)
  shows "list_sel f x y = foldr (\<lambda>b a. a * list_sel_aux f b y) x 1"
*)

end