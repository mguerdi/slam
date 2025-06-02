signature JEHA_SYMBOL_TABLE =
sig
  include TABLE
  val add_symbols : term -> set -> set
end

structure Jeha_Symbol_Table : JEHA_SYMBOL_TABLE =
struct

open Termtab

fun add_symbol (Const (x, _)) = insert_set (Const (x, dummyT))
  | add_symbol (Free (x, _)) = insert_set (Free (x, dummyT))
  | add_symbol _ = I

val add_symbols = fold_aterms add_symbol

end