signature LCS_LANGUAGE =
sig
  structure V : ABT_OPERATOR where type 'a Ar.Vl.Sp.t = 'a list
  structure K : ABT_OPERATOR where type 'a Ar.Vl.Sp.t = 'a list
  sharing type V.Ar.Vl.Sort.t = K.Ar.Vl.Sort.t

  val input : 'i K.t -> V.Ar.sort
  val opidSort : V.Ar.sort option
end
