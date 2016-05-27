signature LCS_DYNAMICS =
sig
  structure Lcs : LCS_DEFINITION
  structure Closure : LCS_CLOSURE
  sharing type Closure.Abt.Operator.t = Lcs.O.operator

  type 'a closure = 'a Closure.closure
  type abt = Closure.Abt.abt

  val step : abt closure -> abt closure option
end
