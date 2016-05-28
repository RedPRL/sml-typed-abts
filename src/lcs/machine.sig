(* A stack machine for lazy computation systems *)
signature LCS_MACHINE =
sig
  structure Cl : LCS_CLOSURE

  type cont = Cl.Abt.abt
  type expr = Cl.Abt.abt

  type stack = cont Cl.closure list

  (* Our stack machine has two phases of execution. In [c <| S], we are trying
     to run the control term [c] down to a final form. When [c |> S], we know
     that [c] is final; if the stack is S ≡ [], we are done; if S ≡ k ∷ S', then
     we plug [c] into [k], and proceed. *)

  datatype 'a state =
      <| of 'a Cl.closure * stack
    | |> of 'a Cl.closure * stack

  val start : 'a -> 'a state
  val isFinal : expr state -> bool
  val star : (expr state -> expr state) -> expr state -> expr state

  val map : ('a -> 'b) -> 'a state -> 'b state
  val toString : expr state -> string
end
