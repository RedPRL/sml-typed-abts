signature VALENCE =
sig
  type sort
  structure Spine : SPINE

  type bindings =
    {symbols : sort Spine.t,
     variables : sort Spine.t}

  type t = bindings * sort

  structure Show : SHOW where type t = t
  structure Eq : EQ where type t = t
end

