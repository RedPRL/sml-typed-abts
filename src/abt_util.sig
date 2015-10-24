signature ABT_UTIL =
sig
  include ABT

  (* abt patterns of variable depth *)
  datatype star = STAR of star view | EMB of abt
  val checkStar : metacontext -> star * valence -> abt
end

