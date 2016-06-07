(* A stack machine for lazy computation systems *)
signature LCS_MACHINE =
sig
  structure Cl : LCS_CLOSURE
  structure K : ABT_OPERATOR

  datatype ('o, 'a) pat = `$ of 'o * 'a Cl.Abt.bview list

  type expr = Cl.Abt.abt

  type cont = (Cl.Abt.symbol K.t, expr Cl.closure) pat
  type stack = cont list

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
