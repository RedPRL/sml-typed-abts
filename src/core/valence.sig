(* A valence is the "type" assigned to each abstraction in the framework
 * of abts. It includes 3 things
 *
 *  - The sorts of all the bound variables
 *  - The sort of the actual term once it's been instantiated with all
 *    the appropriate missing pieces
 *)
signature ABT_VALENCE =
sig
  structure S : ABT_SORT

  type sort = S.t
  type 'a spine = 'a list

  (* bindings are lists of variable sorts respectively *)
  type bindings = sort spine
  type t = bindings * sort

  val toString : t -> string
  val eq : t * t -> bool
end

signature UNISORTED_ABT_VALENCE =
sig
  include ABT_VALENCE
    where type S.t = unit

  val make : int -> t
end
