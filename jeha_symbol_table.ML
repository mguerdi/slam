signature JEHA_SYMBOL_TABLE =
sig
  type symbol = term (* a symbol is Const or a Free modulo type (i.e. name only) *)
  type set
  val empty: set
  val symbols: set -> symbol list
  val add_symbols: term -> set -> set
  val aterm_defined: set -> term -> bool
end

structure Jeha_Symbol_Table : JEHA_SYMBOL_TABLE =
struct

(* symbols *)

type symbol = term

fun can_symbol (Const _) = true
  | can_symbol (Free _) = true
  | can_symbol _ = false

fun is_symbol (Const (_, dummyT)) = true
  | is_symbol (Free (_, dummyT)) = true
  | is_symbol _ = false

fun symbol_of (Const (x, _)) = Const (x, dummyT)
  | symbol_of (Free (x, _)) = Free (x, dummyT)

(* symbol set *)

type set = Termtab.set

val empty = Termtab.empty

val symbols = Termtab.keys

fun add_symbol t = if can_symbol t then Termtab.insert_set (symbol_of t) else I

val add_symbols = fold_aterms add_symbol

fun aterm_defined set t =
  if can_symbol t
    then Termtab.defined set (symbol_of t)
    else false

end