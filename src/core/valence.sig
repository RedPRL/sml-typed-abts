(* A valence is the "type" assigned to each abstraction in the framework
 * of abts. It includes 3 things
 *
 *  - The sorts of all the bound symbols
 *  - The sorts of all the bound variables
 *  - The sort of the actual term once it's been instantiated with all
 *    the appropriate missing pieces
 *)
signature ABT_VALENCE =
sig
  structure Sort : ABT_SORT
  structure Spine : SPINE

  type sort = Sort.t
  type 'a spine = 'a Spine.t

  (* bindings are spines of symbol sorts and variable sorts respectively *)
  type bindings = sort spine * sort spine
  type t = bindings * sort

  val toString : t -> string
  val eq : t * t -> bool
end

signature UNISORTED_ABT_VALENCE =
sig
  include ABT_VALENCE
    where type Sort.t = unit
    where type 'a Spine.t = 'a list

  val make : int * int -> t
end
