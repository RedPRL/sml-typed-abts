signature LCS_DYNAMICS =
sig
  structure Lcs : LCS_DEFINITION
  structure Abt : ABT
  sharing type Lcs.O.operator = Abt.Operator.t

  type 'a state

  val inject : 'a -> 'a state
  val project : Abt.abt state -> Abt.abt

  val step : Abt.abt state -> Abt.abt state
  val eval : Abt.abt -> Abt.abt
end
