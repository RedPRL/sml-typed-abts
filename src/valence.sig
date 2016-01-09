(* A valence is the "type" assigned to each abstraction in the framework
 * of abts. It includes 3 things
 *
 *  - The sorts of all the bound symbols
 *  - The sorts of all the bound variables
 *  - The sort of the actual term once it's been instantiated with all
 *    the appropriate missing pieces
 *)
signature VALENCE =
sig
  type sort
  structure Spine : SPINE

  (* bindings are spines of symbol sorts and variable sorts respectively *)
  type bindings = sort Spine.t * sort Spine.t
  type t = bindings * sort

  structure Show : SHOW where type t = t
  structure Eq : EQ where type t = t
end
