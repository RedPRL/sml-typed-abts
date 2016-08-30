signature ABT_PARAMETER =
sig
  include FUNCTOR

  datatype 'a term =
     VAR of 'a
   | APP of 'a term t

  val eq : ('a * 'a -> bool) -> 'a t * 'a t -> bool
  val toString : ('a -> string) -> 'a t -> string

  val join : 'a -> ('a * 'a -> 'a) -> 'a t -> 'a
end

signature ABT_PARAMETER_UTIL =
sig
  structure P : ABT_PARAMETER

  include MONAD where type 'a t = 'a P.term

  val eq : ('a * 'a -> bool) -> 'a t * 'a t -> bool
  val toString : ('a -> string) -> 'a t -> string

  val collectSubterms : 'a P.t -> 'a list
end


