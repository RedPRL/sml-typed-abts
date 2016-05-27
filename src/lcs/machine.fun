functor LcsMachine
  (structure Cl : LCS_CLOSURE
   val isFinal : Cl.Abt.abt -> bool) : LCS_MACHINE =
struct
  structure Cl = Cl

  open Cl

  type cont = Abt.abt
  type expr = Abt.abt

  type stack = cont Cl.closure list
  datatype 'a state = || of 'a Cl.closure * stack

  infix 1 ||
  infix 2 <:

  fun start m =
    new m || []

  val exprIsFinal = isFinal

  fun isFinal (m <: _ || []) = exprIsFinal m
    | isFinal _ = false

  fun star step st =
    if isFinal st then
      st
    else
      star step (step st)
end
