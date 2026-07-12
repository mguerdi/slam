infix 6 +++
infix 6 ---

signature SLAM_WEIGHT =
sig
  type weight
  val make : int -> int -> weight
  val dest : weight -> int * int
  val +++ : weight * weight -> weight
  val --- : weight * weight -> weight
  val negate : weight -> weight
  val ord : weight ord
end;

structure Slam_Weight_Paired : SLAM_WEIGHT =
struct

(* (omega, one) represents the number: omega * \<omega> + one * 1 *)
type weight = int * int;

val make = pair
val dest = I

fun plus_weight (omega, one) (0, one') = (omega, one + one') (* just special-cased *)
  | plus_weight (omega, one) (omega', 0) = (omega + omega', one) (* just special-cased *)
  | plus_weight (omega, one) (omega', one') = (omega + omega', one + one')
fun (w +++ w') = plus_weight w w'
fun negate (omega, one) = (~omega, ~one)
fun (w --- w') = w +++ negate w'

val ord = prod_ord int_ord int_ord

end;

(* claude *)
(* FIXME: crash on overflow *)
structure Packed : sig
  type t = FixedInt.int
  val pack    : FixedInt.int * FixedInt.int -> t        (* (a, b), a is the major key *)
  val unpack  : t -> FixedInt.int * FixedInt.int
  val add     : t * t -> t
  val sub     : t * t -> t
  val neg     : t -> t
  val compare : t * t -> order         (* lexicographic on (a, b) *)
end =
struct
  type t = FixedInt.int
  (* layout:  [ ......... a ......... | k bits of b ] *)
  val k    = 16
  val K    = 0x10000      (* 2^k     *)
  val half = 0x8000       (* 2^(k-1) *)

  fun pack (a, b) = a * K + b

  fun lo v =
      let val r = v mod K              (* 0 <= r < K, since K > 0 *)
      in if r >= half then r - K else r end

  fun hi v = (v - lo v) div K
  fun unpack v = (hi v, lo v)

  fun add (x, y) = x + y
  fun sub (x, y) = x - y
  fun neg x      = ~x
  fun compare (x, y) = FixedInt.compare (x, y)
end

structure Slam_Weight_Packed : SLAM_WEIGHT =
struct

type weight = FixedInt.int

fun make omega one = Packed.pack (FixedInt.fromInt omega, FixedInt.fromInt one)
val dest = apply2 FixedInt.toInt o Packed.unpack

fun plus_weight w1 w2 = w1 + w2

fun (w +++ w') = w + w'
fun negate w = ~w
fun (w --- w') = w + ~w'

val ord = FixedInt.compare

end

(* FIXME: try and compare to a reference-based weight *)
structure Slam_Weight = Slam_Weight_Packed

signature PARTIAL_ORD =
sig
  type partial_order = order option
  val is_equal: partial_order -> bool
  val is_less: partial_order -> bool
  val is_less_equal: partial_order -> bool
  val is_greater: partial_order -> bool
  val is_greater_equal: partial_order -> bool
end

structure Partial_Ord: PARTIAL_ORD =
struct

type partial_order = order option

val is_equal = Slam_Common.some_is is_equal
val is_less = Slam_Common.some_is is_less
val is_less_equal = Slam_Common.some_is is_less_equal
val is_greater = Slam_Common.some_is is_greater
val is_greater_equal = Slam_Common.some_is is_greater_equal

end

(* Transfinite Higher Order Knuth Bendix Ordering *)

signature SLAM_ORDER =
sig
  include SLAM_WEIGHT
  include PARTIAL_ORD
  val weight_ord : Slam_Weight.weight ord
  val zero_weight : Slam_Weight.weight
  val var_weight : Slam_Weight.weight
  val const_weight : Slam_Weight.weight
  val mk_multiset_order_of_strict :
        ('a * 'a -> partial_order) -> ('a list) * ('a list) -> partial_order
  val idxs_of_maximal_elements : ('a * 'a -> partial_order) -> 'a list -> (int * bool) list
  val is_maximal : ('a * 'a -> partial_order) -> bool -> 'a -> 'a list -> bool
  val multiset_eq : ('a * 'a -> bool) -> ('a list * 'a list) -> bool
  val multiset_is_greater_reference :
    ('a * 'a -> bool) -> ('a * 'a -> bool) -> ('a list * 'a list) -> bool
end;

structure Slam_Order: SLAM_ORDER =
struct

open Slam_Weight
open Partial_Ord

val zero_weight = Slam_Weight.make 0 0

(* lexicographic comparison *)
val weight_ord = Slam_Weight.ord

val var_weight = Slam_Weight.make 0 1
val const_weight = Slam_Weight.make 0 1

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
            |> uncurry Slam_Common.cartesian_product
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
    |> map_filter (fn (idx, is_max) => Slam_Common.map_some (pair idx) is_max)
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
