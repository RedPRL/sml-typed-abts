(* This is meant to be an abstraction on top of the way that we implement
 * abt.fun. Specifically, in that development we use efficient DeBruijn indices
 * for bound variables and globally unique identifiers for unbound ones. This
 * gives efficient alpha-equivalence but means we have two distinct kinds
 * of variables lurking about.
 *
 * This signature describes how to glue them together into one type and gives
 * several simple operations upon them.
 *)
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
