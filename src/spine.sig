signature SPINE =
sig
  type 'a t
  val empty : 'a t

  val pretty : ('a -> string) -> string -> 'a t -> string

  structure Functor : FUNCTOR where type 'a t = 'a t

  structure Pair :
  sig
    val mapEq : ('a * 'b -> 'c) -> 'a t * 'b t -> 'c t
    val allEq : ('a * 'b -> bool) -> 'a t * 'b t -> bool
  end
end
