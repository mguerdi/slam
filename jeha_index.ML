(* fingerprint indexing, from the paper
Efficient Full Higher-Order Unification *)

signature JEHA_INDEX =
sig
  datatype feature = 
    AnonymousVar (* A *)
  | BelowVar (* B *)
  | InvalidPosition (* N *)
  (* symbols *)
  | DB of int
  | FOFree of string
  | FOConst of string
  val feature_ord : feature ord
  val feature_at : typ list -> JTerm.tpos -> term -> feature
  (* FIXME: pass tuples *)
  val could_unify : (feature * feature) -> bool
  val could_match : (feature * feature) -> bool
end;

structure Jeha_Index : JEHA_INDEX =
struct

(* see zipperposition Fingerprint.ml *)
datatype feature = 
  AnonymousVar (* A *)
| BelowVar (* B *)
| InvalidPosition (* N *)
(* symbols *)
| DB of int
| FOFree of string
| FOConst of string

fun is_symbol (DB _) = true
  | is_symbol (FOFree _) = true
  | is_symbol (FOConst _) = true
  | is_symbol _ = false

(* In the sense of the translation for fingerprint indexing, i.e. if the head is
a variable or the head's type's return type (domain) is a TVar *)
fun return_is_tvar T = is_TVar (body_type T)

fun is_var_head _ (Var _) = true
  | is_var_head Ts (Bound i) = return_is_tvar (nth Ts i)
  | is_var_head _ (Abs _) = error "abs head encountered (not beta-normal)"
  | is_var_head _ t = return_is_tvar (fastype_of t)

fun feature_of (Free (name, _)) = FOFree name
  | feature_of (Const (name, _)) = FOConst name
  | feature_of (Bound i) = DB i
  | feature_of (Var _) = error "var should have been checked previously"

(* FIXME: if we have to, \<eta>-expand everything before calling this *)
fun feature_at Ts p (Abs (_, T, t)) = feature_at (T::Ts) p t
  | feature_at Ts [] t =
      (* position is \<epsilon>, analyse the head *)
      let val (head, args) = strip_comb t in
      if is_var_head Ts head
        then AnonymousVar
        else feature_of head
      end
  | feature_at Ts (0::_) t = error "can't have 0 position in fingerprint translation"
  | feature_at Ts (i::is) t = 
      let val (head, args) = strip_comb t in
      if is_var_head Ts head
        then BelowVar
      else if i > length args
        then InvalidPosition
      else feature_at Ts is (nth args (i-1))
      end

(* regarding \<eta> long/short:
https://github.com/leanprover-community/duper/blob/ff6e7e5aadc6f9b3080fa3454d993a296d7484c9/Duper/Fingerprint.lean#L130
I'm not sure if I believe this. *)

fun could_unify (f1, f2) =
  let
    (* could_unify_asym implements the following, where
    X = False
       S1 S2  A  B  N
    S1     X  X  X  X
    S2  X     X  X  X
     A              X
     B               
     N  X  X  X      
    transposed:
       S1 S2  A  B  N
    S1     X        X
    S2  X           X      
     A  X  X        X
     B  X  X         
     N  X  X  X      
    disjunction of those two is the desired table.
    *)
      (* full case distinctions when lhs is not a symbol *)
    fun could_unify_asym BelowVar _ = true
      | could_unify_asym AnonymousVar InvalidPosition = false
      | could_unify_asym AnonymousVar _ = true
      | could_unify_asym InvalidPosition BelowVar = true
      | could_unify_asym InvalidPosition InvalidPosition = true
      | could_unify_asym InvalidPosition _ = false
      (* lhs will be a symbol *)
      | could_unify_asym s t = s = t
  in
    (* symmetrize *)
    could_unify_asym f1 f2 orelse could_unify_asym f2 f1
  end

fun could_match (BelowVar, _) = true
  | could_match (AnonymousVar, InvalidPosition) = false
  | could_match (AnonymousVar, BelowVar) = false
  | could_match (InvalidPosition, InvalidPosition) = true
  | could_match (InvalidPosition, _) = false
  (* lhs will be a symbol *)
  | could_match (pattern_feature, target_feature) = pattern_feature = target_feature

(* for use as ordered keys *)
fun to_int AnonymousVar = 0
  | to_int BelowVar = 1
  | to_int InvalidPosition = 2
  | to_int (DB _) = 3
  | to_int (FOFree _) = 4
  | to_int (FOConst _) = 5

fun feature_ord feature_pair = 
  let
    val cmp = (int_ord o apply2 to_int) feature_pair
  in
    if cmp = EQUAL
      then case feature_pair of
        (DB i, DB j) => int_ord (i, j)
      | (FOFree s, FOFree t) => string_ord (s, t)
      | (FOConst s, FOConst t) => string_ord (s, t)
      | (s, t) => if s = t then EQUAL else error "this can't happen"
      else cmp
  end

end;

structure FeatureTable = Table(type key = Jeha_Index.feature val ord = Jeha_Index.feature_ord);

signature FEATURE_TRIE =
sig
  include JEHA_INDEX
  type 'a T
  val empty: 'a T
  val insert : (feature list * 'a) -> 'a T -> 'a T
  val insert_term : JTerm.tpos list -> term -> term T -> term T
  val compute_key : JTerm.tpos list -> term -> feature list
  val fold : (feature * feature -> bool) -> feature list -> ('a -> 'b -> 'b) -> 'a T -> 'b -> 'b
  val get_unifiables : JTerm.tpos list -> term -> term T -> term list
end;

structure FeatureTrie : FEATURE_TRIE =
struct
  open Jeha_Index
  type key = feature list

  datatype 'a T =
    Leaf of 'a list
  | Node of ('a T) FeatureTable.table

  val empty = Node FeatureTable.empty

  fun add_to_leaf x (Leaf xs) = Leaf (x::xs)

  (* add a new 'a to the matching leaf *)
  fun insert ([], value) (Leaf values) = Leaf (value::values)
    | insert ([], _) _  = error "key too short"
    | insert ([k], value) (Node children) = Node (FeatureTable.map_default (k, Leaf []) (add_to_leaf value) children)
    | insert (k::ks, value) (Node children) =
        children
        |> FeatureTable.map_default (k, empty) (insert (ks, value))
        |> Node
    | insert _ _ = error "key too long"
  
  fun compute_key feature_positions t = map (fn p => feature_at [] p t) feature_positions
  
  (* FIXME: we want insert term and subterms *)
  (* FIXME: for testing purposes only *)
  fun insert_term feature_positions t index =
    let
      val key = compute_key feature_positions t
    in
      insert (key, t) index
    end

  (* fold but need to skip branches *)
  (* always look at head of key, decide which branches to descend into, chop head off on recursive calls *)
  (* fold : key -> ('a -> 'b -> 'b) -> 'a T -> 'b -> 'b *)

  (* retrieval *)
  fun fold _ [] f (Leaf xs) acc = Basics.fold f xs acc
    | fold compat (k::ks) f (Node children) acc =
        FeatureTable.fold
          (fn (k', child) => if compat (k, k')
            (* functions that turn accumulators into accumulators: *)
            then fold compat ks f child
            else I)
          children
          acc
    | fold _ [] _ (Node _) _ = error "fold: key too short"
    | fold _ (_::_) _ (Leaf _) _ = error "fold: key too long"

  fun get_unifiables feature_positions t index =
    let
      val key = compute_key feature_positions t
    in
      fold could_unify key cons index []
    end
  
  fun get_instances feature_positions t index =
    let
      val key = compute_key feature_positions t
    in
      fold could_match key cons index []
    end

end;
