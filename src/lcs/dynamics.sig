signature LCS_DYNAMICS =
sig
  structure L : LCS_LANGUAGE
  structure M : LCS_MACHINE

  val run : M.expr M.state -> M.expr

  type sign

  val step : sign -> M.expr M.state -> M.expr M.state
  val eval : sign -> M.expr -> M.expr

  val debugTrace : sign -> M.expr -> unit
end
