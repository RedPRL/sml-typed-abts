signature LCS_MACHINE =
sig
  structure Cl : LCS_CLOSURE

  type cont = Cl.Abt.abt
  type expr = Cl.Abt.abt

  type stack = cont Cl.closure list
  datatype 'a state = || of 'a Cl.closure * stack

  val start : 'a -> 'a state
  val isFinal : expr state -> bool
  val star : (expr state -> expr state) -> expr state -> expr state

  val map : ('a -> 'b) -> 'a state -> 'b state
  val toString : expr state -> string
end
