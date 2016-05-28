signature LCS_LANGUAGE =
sig
  structure V : OPERATOR where type 'a Arity.Valence.Spine.t = 'a list
  structure K : OPERATOR where type 'a Arity.Valence.Spine.t = 'a list
  sharing type V.Arity.Valence.Sort.t = K.Arity.Valence.Sort.t

  val input : 'i K.t -> V.Arity.sort
  val opidSort : V.Arity.sort option
end
