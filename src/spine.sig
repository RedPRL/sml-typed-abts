signature SPINE =
sig
  type 'a t
  type path

  val empty : 'a t

  val isEmpty : 'a t -> bool
  val pretty : ('a -> string) -> string -> 'a t -> string

  val all : ('a -> bool) -> 'a t -> bool

  structure Functor : FUNCTOR
    where type 'a t = 'a t

  structure Foldable : FOLDABLE
    where type 'a t = 'a t

  structure Pair :
  sig
    val mapEq : ('a * 'b -> 'c) -> 'a t * 'b t -> 'c t
    val zipEq : 'a t * 'b t -> ('a * 'b) t
    val allEq : ('a * 'b -> bool) -> 'a t * 'b t -> bool
  end

end
