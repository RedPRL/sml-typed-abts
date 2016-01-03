signature COORD =
sig
  type t
  val origin : t
  val shiftRight : t -> t
  val shiftDown : t -> t

  structure Eq : EQ where type t = t
end

