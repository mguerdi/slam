(* Problem: Isabelle/HOL doesn't have explicit type arguments like o\<lambda>Sup
which are needed for KBO.
Solution: Define o\<lambda>Sup type args as of function symbol f as positions ... *)

(* FIXME: use typ_unify or similar if this is module really needed *)
signature JEHA_POLYMORPHISM =
sig
  generalize_with_term : term -> int list list Symtab.table
end

structure Jeha_Polymorphism =
struct

val tvar_positions = 
  let
    fun impl_tvar_positions pos (TVar ix) = [pos]
      | impl_tvar_positions pos (TFree ix) = []
      | impl_tvar_positions pos (Type (_, Ts)) =
          flat (map_index (fn (i, T) => impl_tvar_positions (i :: pos) T) Ts)
  in
    impl_tvar_positions []
  end

fun is_above (pos1, pos2) = is_prefix (op =) (rev pos2) (rev pos1)
fun is_below (pos1, pos2) = is_prefix (op =) (rev pos1) (rev pos2)

(* generalize two instantiatons of the same type *)
fun most_general_tvar_positions inst1 inst2 =
  let 
    fun generalize pos poss =
      if exists (fn p => is_below (pos, p)) poss
        then poss (* pos is generalized by poss *)
        else pos :: filter (fn p => is_above (p, pos)) poss (* pos generalizes some of poss *)
  in
    fold generalize inst1 inst2
  end

(* FIXME: assuming Const and Free namespaces are distinct *)
(* add type of function symbol to collection, generalizing when one is already present *)
fun generalize_with_aterm (Const (name, T)) =
      let
        val tposs = tvar_positions T
      in
        Symtab.map_default (name, tposs) (most_general_tvar_positions tposs)
      end
  | generalize_with_aterm (Free (name, T)) =
      let
        val tposs = tvar_positions T
      in
        Symtab.map_default (name, tposs) (most_general_tvar_positions tposs)
      end
  | generalize_with_aterm (Var _) = I

val generalize_with_term = fold_aterms generalize_with_aterm

end;