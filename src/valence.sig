signature VALENCE =
sig
  type sort
  structure Spine : SPINE

  (* bindings are lists of symbol sorts and variable sorts respectively *)
  type bindings = sort Spine.t * sort Spine.t
  type t = bindings * sort

  structure Show : SHOW where type t = t
  structure Eq : EQ where type t = t
end

