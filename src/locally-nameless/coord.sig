(* A moveable description of the position of something. This is used to
 * generalize a DeBruijn index. It points to the location of a abstraction
 * from a term.
 *
 * In our usage the x coordinate tells us where the abstraction is and the y
 * coordinate tells us which item in the abstraction we're using.
 *)
signature LN_COORD =
sig
  type t
  val origin : t
  val shiftRight : t -> t
  val shiftDown : t -> t

  val eq : t * t -> bool
  val toString : t -> string
end
