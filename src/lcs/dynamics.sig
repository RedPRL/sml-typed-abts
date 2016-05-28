signature LCS_DYNAMICS =
sig
  structure L : LCS_LANGUAGE
  structure M : LCS_MACHINE
  structure Sig : LCS_SIGNATURE

  val run : M.expr M.state -> M.expr

  val step : Sig.t -> M.expr M.state -> M.expr M.state
  val eval : Sig.t -> M.expr -> M.expr

  val debugTrace : Sig.t -> M.expr -> unit
end
