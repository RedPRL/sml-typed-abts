signature LCS_DYNAMICS =
sig
  structure Lcs : LCS_DEFINITION
  structure M : LCS_MACHINE

  sharing type Lcs.O.operator = M.Cl.Abt.Operator.t

  val run : M.expr M.state -> M.expr

  type sign

  val step : sign -> M.expr M.state -> M.expr M.state
  val eval : sign -> M.expr -> M.expr

  val debugTrace : sign -> M.expr -> unit
end
