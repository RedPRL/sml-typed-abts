signature LOCALLY_NAMELESS =
sig
  structure Coord : COORD

  datatype 'a t =
      FREE of 'a
    | BOUND of Coord.t

  structure Eq : EQ1 where type 'a t = 'a t
  structure Functor : FUNCTOR where type 'a t = 'a t
  structure Monad : MONAD where type 'a t = 'a t

  exception UnexpectedBoundName of Coord.t

  (* raises UnexpectedBoundName *)
  val getFree : 'a t -> 'a
end
