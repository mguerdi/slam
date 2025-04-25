
signature ID_GENERATOR =
sig
  val new : unit -> int
end;

functor Id_Generator(val name: string) : ID_GENERATOR =
struct

(* FIXME: why do we need this? Doesn't the prover run in a single thread? If not, how can we get one
id generator per prover instance? *)
local
  val lock = Thread.Mutex.mutex ();
in
  fun critical e () = Multithreading.synchronized name lock e
end;

(* basically newId from metis.ML *)
val new  =
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

structure JClause_Id : ID_GENERATOR = Id_Generator(val name = "jeha_clause_id")

structure JSkolem_Id : ID_GENERATOR = Id_Generator(val name = "jeha_skolem_id")
