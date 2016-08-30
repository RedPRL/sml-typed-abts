signature ABT_MACHINE_STATE =
sig
  structure Cl : ABT_CLOSURE

  datatype 'a plus = HOLE | % of 'a
  type 'a kont = ('a, 'a) Cl.closure plus Cl.Abt.appview
  type 'a frame = 'a kont * (Cl.Abt.symbol list * Cl.Abt.variable list)
  type 'a focus = ('a, 'a) Cl.closure
  type 'a stack = 'a frame list

  datatype mode =
     DOWN
   | UP
   | UNLOAD

  type 'a state = mode * 'a focus * 'a stack

  datatype 'a step =
     STEP of ('a, 'a) Cl.closure
   | CUT of ('a plus Cl.Abt.appview * 'a, 'a) Cl.closure
   | VAL
end

signature ABT_MACHINE_BASIS =
sig
  structure M : ABT_MACHINE_STATE where type 'a Cl.Abt.O.Ar.Vl.Sp.t = 'a list
  type abt = M.Cl.Abt.abt

  val step : (abt M.Cl.Abt.appview, abt) M.Cl.closure -> abt M.step
  val plug : abt M.kont * abt M.focus M.Cl.Abt.bview -> abt M.focus option
end

signature ABT_MACHINE =
sig
  include ABT_MACHINE_BASIS

  val load : abt -> abt M.state
  val next : abt M.state -> abt M.state option
end


