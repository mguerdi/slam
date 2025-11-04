signature SLAM_FUEL =
sig
  type fuel
  exception FUEL
  val new : int -> fuel
  (* call to consume fuel, returns remainig fuel *)
  val consume : int -> fuel -> unit (* exception FUEL *)
  val map_consume : int -> fuel -> ('a -> 'b) -> 'a Seq.seq -> 'b Seq.seq (*exception FUEL*)
  val fuelled : 'a Seq.seq (*exception FUEL*) -> 'a Seq.seq
end

structure Slam_Fuel : SLAM_FUEL =
struct

type fuel = int Unsynchronized.ref

exception FUEL

fun new (amount: int) = Unsynchronized.ref amount

fun consume (use: int) (fuel: fuel) : unit =
  let
    val current_fuel = !fuel
    val new_fuel = current_fuel - use
  in
    if new_fuel < 0 then raise FUEL else (fuel := new_fuel)
  end

fun map_consume (use: int) (fuel: fuel) (f: 'a -> 'b) (sequence: 'a Seq.seq) : 'b Seq.seq =
  Seq.make (fn () =>
    (
    consume use fuel;
    case Seq.pull sequence of
      SOME (head, tail) => SOME (f head, map_consume use fuel f tail)
    | NONE => NONE
    )
  )

fun fuelled (sequence : 'a Seq.seq (*exception FUEL*)) =
  Seq.make (fn () =>
    case (Seq.pull sequence handle FUEL => NONE) of
      SOME (head, tail) => 
          SOME (head, fuelled tail)
    | NONE => NONE
  )

end