signature LCS_UTIL =
sig
  structure Abt : ABT

  val neutral : Abt.abt -> bool
end
