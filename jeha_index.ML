(* fingerprint indexing, from the paper
Efficient Full Higher-Order Unification *)

(* Const and Free *)
signature JEHA_SYMBOL =
sig
  type symbol
  val of_term : term -> symbol
end;

structure Jeha_Symbol =
struct
  type symbol = term

  fun of_term (t as Free _) = t
    | of_term (t as Const _) = t
    | of_term _ = error "can only convert Free or Const to symbol"
end;

signature JEHA_FINGERPRINT =
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

structure Jeha_Fingerprint : JEHA_FINGERPRINT =
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
a variable or the head's type's return type (domain) is a TVar
   Q: What if it contains a TVar? Why is that okay?
   A: Probably because only function types can lead to eta expansion?
   Q: Okay, but what if the return type is a type synonym for a function type?
   A: ??? (not possible?)
*)
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

signature JEHA_TRIE =
sig
  type 'a T (* The Trie itself *)
  structure FeatureTable : TABLE;
  type key = FeatureTable.key list
  val empty: 'a T
  val insert : (key * 'a) -> 'a T -> 'a T
  val fold : (FeatureTable.key * FeatureTable.key -> bool) -> key -> ('a -> 'b -> 'b) -> 'a T -> 'b -> 'b
end;


(* feature is
    * for green subterms: Jeha_Index.feature
    * for subsumption: numbers based on the translation from Jeha_Index *)
functor Jeha_Trie(structure FeatureTable : TABLE) : JEHA_TRIE =
struct
  structure FeatureTable = FeatureTable;
  (* FIXME: DELETE open Jeha_Index *)
  (* FIXME: DELETE type feature = feature *)
  type key = FeatureTable.key list

  (* A Trie storing lists of 'a. *)
  datatype 'a T =
    Leaf of 'a list
  | Node of ('a T) FeatureTable.table

  val empty = Node FeatureTable.empty

  fun add_to_leaf x (Leaf xs) = Leaf (x::xs)

  (* add a new 'a to the matching leaf *)
  fun insert ([], value) (Leaf values) = Leaf (value::values)
    | insert ([], _) _  = error "key too short"
    | insert ([k], value) (Node children) =
        Node (FeatureTable.map_default (k, Leaf []) (add_to_leaf value) children)
    | insert (k::ks, value) (Node children) =
        children
        |> FeatureTable.map_default (k, empty) (insert (ks, value))
        |> Node
    | insert _ _ = error "key too long"
  
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
end;

(* Index for green subterms, etc. *)

signature TERM_INDEX =
sig
  include JEHA_TRIE
  val insert_term : JTerm.tpos list -> term -> term T -> term T
  val compute_key : JTerm.tpos list -> term -> key
  val get_unifiables : JTerm.tpos list -> term -> term T -> term list
  val get_instances : JTerm.tpos list -> term -> term T -> term list
end;


structure Term_Index : TERM_INDEX =
struct
  structure FPFeatureTable : TABLE = Table(type key = Jeha_Fingerprint.feature val ord = Jeha_Fingerprint.feature_ord);
  structure Term_Index_Trie = Jeha_Trie(structure FeatureTable = FPFeatureTable);

  open Term_Index_Trie

  fun compute_key feature_positions t = map (fn p => Jeha_Fingerprint.feature_at [] p t) feature_positions
  
  fun get_unifiables feature_positions t index =
    let
      val key = compute_key feature_positions t
    in
      fold Jeha_Fingerprint.could_unify key cons index []
    end
  
  fun get_instances feature_positions t index =
    let
      val key = compute_key feature_positions t
    in
      fold Jeha_Fingerprint.could_match key cons index []
    end

  (* FIXME: we want insert term and subterms *)
  (* FIXME: for testing purposes only *)
  fun insert_term feature_positions t index =
    let
      val key = compute_key feature_positions t
    in
      insert (key, t) index
    end
end;

signature SUBSUMPTION_INDEX =
sig
  include JEHA_TRIE
  type feature_fun
  (* Only FOFree or FOConst as first arg! *)
  val compute_key : feature_fun list -> JClause.T -> key
  val symbols_with_max_depth : term -> int Termtab.table
  val symbols_with_min_depth : term -> int Termtab.table
end;

(* FIXME: aggregate features (i.e. all depths) into sets, maps like zipperposition's FV_Tree.ml *)


structure Subsumption_Index : SUBSUMPTION_INDEX =
struct
  datatype subsumption_feature =
    Number of int
  | Map of int Termtab.table

  fun subsumption_ord (left : subsumption_feature, right : subsumption_feature) = error ""

  structure Subsumption_Index_Trie =
    Jeha_Trie(structure FeatureTable =
      Table(type key = subsumption_feature val ord = subsumption_ord)
    );

  open Subsumption_Index_Trie

  type feature_fun = JClause.T -> FeatureTable.key
  
  (* features *)
  (* independent of signature *)
  val num_positive = JClause.literals #> filter JLit.is_positive #> length
  val num_negative = JClause.literals #> filter (not o JLit.is_positive) #> length
  (* signature dependent (FIXME) *)
  
  (* do we need something like symbol present / not present?
  Or is this already covered by max_depth of symbol etc.?

  Suppose symbol f is present. Then f will have a max depth d.
  Otherwise the max depth feature for f will be 0. (?)
  In zipperposition does the first guard the second?
  Can we do ~1 if the symbol is not present?
  *)

  (* compare zipperposition FV_tree.ML:182 (symbols_depth) *)
  (* FIXME: collect all features with one traversal *)
  fun symbols_with_depth combine t =
    let
      fun add_term (info : JTerm.fold_state) t depth_map = 
          let
            val { lvl = lvl, depth = depth, ... } = info
            val depth_without_lambdas = depth - lvl
            val is_leaf = JTerm.is_variable_headed t
            val depth_map =
              if is_Free t orelse is_Const t (* => not is_leaf *)
                then Termtab.map_entry t (combine depth_without_lambdas) depth_map
                else depth_map
          in
            (* FIXME: Can we count typed Bound as a symbol "in the same way"
            that fingerprint indexing does? *)
            (* FIXME: do we consider head with polymorphic return types to be
            variables? like above. Probably no *)
            (depth_map, is_leaf)
          end
    in
      JTerm.fold_preorder_augmented add_term t Termtab.empty
    end

  val symbols_with_max_depth = symbols_with_depth (curry Int.max)

  val symbols_with_min_depth = symbols_with_depth (curry Int.min)

  fun compute_key features clause = map (fn f => f clause) features
end;

(* FIXME: same structure again but with flat int features *)