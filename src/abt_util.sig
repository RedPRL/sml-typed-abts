signature ABT_UTIL =
sig
  include ABT

  datatype star = STAR of star view | EMB of abt
  val checkStar : star * valence -> abt
end

