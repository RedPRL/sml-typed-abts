signature ARITY =
sig
  structure Sort : SORT
  structure Valence : VALENCE
  sharing type Valence.sort = Sort.t

  type t = Valence.t Valence.Spine.t * Sort.t
  structure Show : SHOW where type t = t
  structure Eq : EQ where type t = t
end


