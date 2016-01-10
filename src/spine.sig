(* A spine is an abstraction over the sequences of symbols and variables
 * that occur in abstractions, applications of metavariables, and anywhere else.
 *
 * The extra level of generality given by making t polymorphic means that
 * the same sort of spine can be used to store both symbols, variables, or whatever
 * else we need.
 *)
signature SPINE =
sig
  type 'a t

  val empty : unit -> 'a t
  val isEmpty : 'a t -> bool
  val pretty : ('a -> string) -> string -> 'a t -> string

  val all : ('a -> bool) -> 'a t -> bool
  val exists : ('a -> bool) -> 'a t -> bool

  structure Functor : FUNCTOR
    where type 'a t = 'a t

  structure Foldable : FOLDABLE
    where type 'a t = 'a t

  structure Pair :
  sig
    exception UnequalLengths
    val mapEq : ('a * 'b -> 'c) -> 'a t * 'b t -> 'c t
    val zipEq : 'a t * 'b t -> ('a * 'b) t
    val allEq : ('a * 'b -> bool) -> 'a t * 'b t -> bool
  end
end
