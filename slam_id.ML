
signature ID_GENERATOR =
sig
  val init : Proof.context -> unit
  val new : Proof.context -> unit -> int
end;

functor Proof_Context_Id_Generator(val name: string) : ID_GENERATOR =
struct

structure Counter = Proof_Data(type T = int Unsynchronized.ref val init = K (Unsynchronized.ref 0))

fun init ctxt = (Counter.get ctxt) := 0

fun new ctxt () =
  let
    val counter = Counter.get ctxt
    val old = !counter
    val () = counter := old + 1
  in
    old
  end

end

functor Mutex_Id_Generator(val name: string) : ID_GENERATOR =
struct

(* FIXME: why do we need this? Doesn't the prover run in a single thread? If not, how can we get one
id generator per prover instance? *)
local
  val lock = Thread.Mutex.mutex ();
in
  fun critical e () = Multithreading.synchronized name lock e
end;

val init = K ()

(* basically newId from metis.ML *)
fun new ctxt =
  let
    (* the next id that will be given out *)
    val counter = Unsynchronized.ref 0
    fun next_id _ =
      let
        val Unsynchronized.ref new_id = counter
        val () = counter := new_id + 1
      in
        new_id
      end
  in
    fn () => critical next_id ()
  end

end;

structure JClause_Id : ID_GENERATOR = Proof_Context_Id_Generator(val name = "slam_clause_id")

structure JSkolem_Id : ID_GENERATOR = Proof_Context_Id_Generator(val name = "slam_skolem_id")
