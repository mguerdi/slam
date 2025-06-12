infix 6 +++
infix 6 ---

signature JEHA_WEIGHT =
sig
  type weight = int * int
  val +++ : weight * weight -> weight 
  val --- : weight * weight -> weight
  val negate : weight -> weight
end;

structure Jeha_Weight : JEHA_WEIGHT =
struct

(* (omega, one) represents the number: omega * \<omega> + one * 1 *)
type weight = int * int;

fun plus_weight (omega, one) (omega', one') = (omega + omega', one + one')
fun (w +++ w') = plus_weight w w'
fun negate (omega, one) = (~omega, ~one)
fun (w --- w') = w +++ negate w'

end;

(* Transfinite Higher Order Knuth Bendix Ordering *)

signature JEHA_ORDER =
sig
  include JEHA_WEIGHT
  type partial_order = order option
  val weight_ord : weight ord
  val zero_weight : weight
  val var_weight : weight
  val const_weight : weight
  val mk_multiset_order_of_strict :
        ('a * 'a -> partial_order) -> ('a list) * ('a list) -> partial_order
  val idxs_of_maximal_elements : ('a * 'a -> partial_order) -> 'a list -> (int * bool) list
  val is_maximal : ('a * 'a -> partial_order) -> bool -> 'a -> 'a list -> bool
  val multiset_eq : ('a * 'a -> bool) -> ('a list * 'a list) -> bool
  val multiset_is_greater_reference :
    ('a * 'a -> bool) -> ('a * 'a -> bool) -> ('a list * 'a list) -> bool
end;

structure Jeha_Order: JEHA_ORDER =
struct

open Jeha_Weight

type partial_order = order option

val zero_weight = (0, 0)

(* lexicographic comparison *)
val weight_ord = prod_ord int_ord int_ord

val var_weight = (0, 1)
val const_weight = (0, 1)

fun multiset_eq a_eq (m, n) = submultiset a_eq (m, n) andalso submultiset a_eq (n, m)

fun multiset_is_greater_reference a_g a_eq (m, n) =
  let
    (* val a_eq = a_ord #> curry op= EQUAL *)
    (* x - y *)
    fun sub x y = fold (remove1 a_eq) y x
  in
    (* M = N *)
    not (multiset_eq a_eq (m, n)) andalso
    forall (fn x => exists (fn y => a_g (y, x)) (sub m n)) (sub n m)
  end

(* Baader and Nipkow - Term rewriting and all that, Lemma 2.5.6: For strict orders:
    M > N iff. M \<noteq> N \<and> \<forall> m \<in> N-M. \<exists> m \<in> M-N. m > n
M < N := N > M *)
(* FIXME: test against a reference implementation *)
fun mk_multiset_order_of_strict a_ord (m, n) =
  if multiset_is_greater_reference (a_ord #> curry op= (SOME GREATER)) (a_ord #> curry op= (SOME EQUAL)) (m, n)
    then SOME GREATER
  (* NOTE: The commented next line is not the same as the line below it! *)
  (*      multiset_is_greater_reference (a_ord #> curry op= (SOME LESS))    (a_ord #> curry op= (SOME EQUAL)) (m, n) *)
  else if multiset_is_greater_reference (a_ord #> curry op= (SOME GREATER)) (a_ord #> curry op= (SOME EQUAL)) (n, m)
    then SOME LESS
  else if multiset_eq (a_ord #> curry op= (SOME EQUAL)) (m, n)
    then SOME EQUAL
  else NONE

(* FIXME: broken, multiset extension of > is not the same as multiset extension of < *)
(*
  let
    fun a_eq (x, y) = SOME EQUAL = a_ord (x, y)
    val m_minus_n = fold (remove1 a_eq) n m
    val n_minus_m = fold (remove1 a_eq) m n
    (* FIXME: what if empty? *)
    val for_m_exists = map (K false) m
    val for_n_exists = map (K false) n
  in
    if null n_minus_m andalso null m_minus_n
      then SOME EQUAL
      else
        let
          val indexed_m_n_pairs =
            (m_minus_n, n_minus_m)
            |> apply2 (map_index (uncurry pair))
            |> uncurry Jeha_Common.cartesian_product
          val (for_m_exists, for_n_exists) =
            (for_m_exists, for_n_exists)
            |> fold
                (fn ((m_idx, m), (n_idx, n)) =>
                  case a_ord (m, n) of
                    SOME GREATER => apsnd (nth_map n_idx (K true))
                  | SOME LESS => apfst (nth_map m_idx (K true))
                  | _ => I)
                indexed_m_n_pairs
        in
          if forall I for_m_exists
            then SOME GREATER
          else if forall I for_n_exists
            then SOME LESS
          else NONE
        end
  end
*)

(* returns the indices of the maximal elements, marked as strict / non-strict by true / false resp. *)
fun idxs_of_maximal_elements a_ord xs =
  let
    val indexed_xs =  map_index (uncurry pair) xs
    (* SOME true: strict maximal, SOME false: non strict maximal, NONE: not maximal *)
    val maximality_markers = map (K (SOME true)) xs
    (* compare the list elements pairwise and determine which are not (strictly) maximal *)
    val maximality_markers =
      fold
      ( fn (i, x) =>
          fold
          ( fn (j, y) => case a_ord (x, y) of 
                SOME GREATER =>
                  (* y cannot be maximal *)
                  nth_map j (K NONE)
              | SOME LESS =>
                  (* x cannot be maximal *)
                  nth_map i (K NONE)
              | SOME EQUAL => (fn markers =>
                  markers |> (case (nth markers i) of
                    (* x and y are equal, so neither is strict maximal.
                    NOTE: this can only happen with the first y that is equal to x *)
                    SOME true => nth_map j (K (SOME false)) #> nth_map i (K (SOME false))
                  | SOME false => nth_map i (K (SOME false))
                  | NONE => nth_map j (K NONE)))
              | NONE => I
          )
          (* compare with all elements which come later in the list *)
          (drop (i + 1) indexed_xs)
      )
      indexed_xs
      maximality_markers
  in
    maximality_markers
    |> map_index (uncurry pair)
    |> map_filter (fn (idx, is_max) => Jeha_Common.map_some (pair idx) is_max)
  end

fun is_maximal a_ord strict x xs =
  let
    (* NONE = not maximal, SOME strict = strict maximal *)
    val (maximal, occurrences) = 
      fold (fn y => fn (maximal, occurrences) =>
        if maximal andalso (not strict orelse occurrences <= 1)
          then case a_ord (y, x) of
            (* y is strictly greater than x, so x can't be maximal *)
            SOME GREATER => (false, occurrences)
          | SOME EQUAL => (true, occurrences + 1)
          | SOME LESS => (true, occurrences)
          | NONE => (true, occurrences)
          (* early abort *)
          else (false, occurrences))
      xs
      (true, 0)
    in
      maximal andalso (not strict orelse occurrences <= 1)
    end

end;
