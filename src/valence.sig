signature VALENCE =
sig
  type sort
  structure Spine : SPINE
  type t = sort Spine.t * sort

  structure Show : SHOW where type t = t
  structure Eq : EQ where type t = t
end

