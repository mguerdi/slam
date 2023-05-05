(* Wrapper around Isabelles unfication functions, needed because of the following remark in unify.ML:
"The outermost functions assume the terms to be unified already have the same type." *)

signature JEHA_UNIFY =
sig
  (* from unify.ML *)
  val smash_unifiers: Context.generic -> (term * term) list -> Envir.env -> Envir.env Seq.seq
  (* from more_unify.ML *)
  val matchers: Context.generic -> (term * term) list -> Envir.env Seq.seq
end

structure Jeha_Unify : JEHA_UNIFY =
struct

fun give_to_undefined t =
  let
    val T = fastype_of t
  in
    (* FIXME: there is a function with this type, maybe better than undefined *)
    Const (@{const_name undefined}, T --> @{typ unit}) $ t
  end

fun smash_unifiers context tus env =
  Unify.smash_unifiers context (map (apply2 give_to_undefined) tus) env
  
fun matchers context pairs =
  Unify.matchers context (map (apply2 give_to_undefined) pairs)

end