signature LAZY_INTF =
sig
  type 'a lazy
  val value: 'a -> 'a lazy
  val lazy: (unit -> 'a) -> 'a lazy
  val force: 'a lazy -> 'a
  val is_finished: 'a lazy -> bool
end

structure DefaultLazy : LAZY_INTF = struct open Lazy end

signature SIMPLE_LAZY =
sig
  include LAZY_INTF
end

structure SimpleLazy : SIMPLE_LAZY =
struct

datatype 'a content = Value of 'a | Expr of unit -> 'a

type 'a lazy = 'a content Unsynchronized.ref

fun value x = Unsynchronized.ref (Value x)
fun lazy f = Unsynchronized.ref (Expr f)
fun the_value r = case !r of Value x => x | Expr _ => error "the_value: not a value"
fun force_eval r = case !r of Expr f => r := Value (f ()) | Value _ => ()
fun force r = (force_eval r; the_value r)
fun is_finished r = case !r of Value _ => true | Expr _ => false

end

structure CacheLazy : SIMPLE_LAZY =
struct

type 'a lazy = 'a Synchronized.cache

fun value x = Synchronized.cache (K x)
fun lazy f = Synchronized.cache f
fun force r = Synchronized.cache_eval {persistent=true} r
fun is_finished r = is_some (Synchronized.cache_peek r)

end

signature RETAIN_LAZY =
sig
  (* Idea: this either contains
    * the result of a lazy computation, or
    * the original input
  Use case:
    * If the lazy computation is finished, the user never cares about the original input.
    * If the lazy computation is not finished, the user might want to either
      * force it to finish
      * discard it and do something else with the original value

  Motivation:
    Suppose we have a value x, and two function f, g such that
      g x = g (f x)
    E.g. f = norm and g = norm_env env.
      With Lazy.lazy we can only store a lazified (f x).
      If later, it turns out that we have to do g, we must still compute f x even though doing only
      g to the original x would've been enough. *)
  type 'a lazy
  val value: 'a -> 'a lazy
  val lazy: ('a -> 'a) -> 'a -> 'a lazy
  val get_any : 'a lazy -> 'a
  val force : 'a lazy -> 'a
  val is_finished : 'a lazy -> bool
end

structure SimpleRetainLazy : RETAIN_LAZY =
struct

datatype 'a content = Value of 'a | Expr of ('a -> 'a) * 'a

type 'a lazy = 'a content Unsynchronized.ref

fun value x = Unsynchronized.ref (Value x)
fun lazy f x = Unsynchronized.ref (Expr (f, x))
fun content_get_any (Value x) = x
  | content_get_any (Expr (_, x)) = x
fun get_any r = content_get_any (!r)
fun the_value r = case !r of Value x => x | Expr _ => error "the_value: not a value"
fun force_eval r = case !r of Expr (f, x) => r := Value (f x) | Value _ => ()
fun force r = (force_eval r; the_value r)
fun is_finished r = case !r of Value _ => true | Expr _ => false

end

(* 10-20% perf overhead on inj_pair over SimpleRetainLazy *)
structure CacheRetainLazy : RETAIN_LAZY =
struct

local

datatype 'a cache_state =
    Undef
  | Value of 'a
  | Weak_Ref of 'a Unsynchronized.weak_ref;

fun peek Undef = NONE
  | peek (Value x) = SOME x
  | peek (Weak_Ref r) = Unsynchronized.weak_peek r;

fun weak_active (Weak_Ref r) = Unsynchronized.weak_active r
  | weak_active _ = false;

in

abstype 'a cache =
  Cache of {f: 'a -> 'a, x: 'a, var: 'a cache_state Synchronized.var}
with

fun cache f x =
  Cache {f = f, x = x, var = Synchronized.var "Synchronized.cache" Undef};

fun cache_peek (Cache {var, ...}) = peek (Synchronized.value var);

fun get_initial (Cache {x, ...}) = x;

fun cache_eval {persistent} (Cache {f, x, var}) =
  Synchronized.change_result var (fn state =>
    let
      val result =
        (case peek state of
          SOME result => result
        | NONE => f x);
      val state' =
        if persistent then Value result
        else if weak_active state then state
        else Weak_Ref (Unsynchronized.weak_ref result);
    in (result, state') end);

end

end

type 'a lazy = 'a cache
fun force_eval r = (cache_eval {persistent=true} r; ())
fun force r = cache_eval {persistent=true} r
fun value x =
  let
    val r = cache I x
    val () = force_eval r
  in
    r
  end
val lazy = cache
fun get_any r =
  case cache_peek r of
    NONE => get_initial r
  | SOME y => y

fun is_finished r = is_some (cache_peek r)

end

(* This bad because it retains the orignal value forever instead of discarding it after the
computation has finished. *)
functor RetainLazy(Lazy : LAZY_INTF) : RETAIN_LAZY =
struct

type 'a lazy = 'a option * 'a Lazy.lazy

fun value x = (NONE, Lazy.value x)

fun lazy f x = (SOME x, Lazy.lazy (fn () => f x))

fun get_any (NONE, y) = Lazy.force y (* only called if y is a Lazy.value *)
  | get_any (SOME x, y) =
      if Lazy.is_finished y
        then Lazy.force y (* only called if y is already finished *)
        else x

fun force (_, y) = Lazy.force y

fun is_finished (_, y) = Lazy.is_finished y

end
