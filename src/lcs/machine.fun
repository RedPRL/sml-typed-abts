functor LcsMachine
  (structure Cl : LCS_CLOSURE
   val isFinal : Cl.Abt.abt Cl.closure -> bool) : LCS_MACHINE =
struct
  structure Cl = Cl

  open Cl

  type cont = Abt.abt
  type expr = Abt.abt

  type stack = cont Cl.closure list

  datatype 'a state =
      <| of 'a Cl.closure * stack
    | |> of 'a Cl.closure * stack

  infix 1 <| |>
  infix 2 <:

  fun start m =
    new m <| []

  val closureIsFinal = isFinal

  fun isFinal (cl |> []) = closureIsFinal cl
    | isFinal _ = false

  fun star step st =
    if isFinal st then
      st
    else
      star step (step st)

  fun map f =
    fn cl <| st => Cl.map f cl <| st
     | cl |> st => Cl.map f cl |> st

  val rec stackToString =
    fn [] => "[]"
     | x :: xs => Cl.toString x ^ " :: " ^ stackToString xs

  val toString =
    fn cl <| st => Cl.toString cl ^ " <| " ^ stackToString st
     | cl |> st => Cl.toString cl ^ " |> " ^ stackToString st
end
