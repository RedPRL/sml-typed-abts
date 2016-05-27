signature LCS_LANGUAGE =
sig
  structure V : OPERATOR where type 'a Arity.Valence.Spine.t = 'a list
  structure K : OPERATOR where type 'a Arity.Valence.Spine.t = 'a list
  sharing type V.Arity.Valence.Sort.t = K.Arity.Valence.Sort.t

  structure P : LCS_PATTERN

  val input : 'i K.t -> V.Arity.sort
  val opidSort : V.Arity.sort option

  type ('s, 'v, 't) value = ('s, 'v, 's V.t, 't) P.pat
  type ('s, 'v, 't) cont = ('s, 'v, 's K.t, 't) P.pat

  val plug : ('s, 'v, 't) cont -> ('s, 'v, 't) value -> ('s, 'v, 't) P.closure
end
