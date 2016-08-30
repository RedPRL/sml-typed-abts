signature ABT_PARAMETER =
sig
  include FUNCTOR

  val eq : ('a * 'a -> bool) -> 'a t * 'a t -> bool
  val toString : ('a -> string) -> 'a t -> string

  val join : 'a -> ('a * 'a -> 'a) -> 'a t -> 'a
end

signature ABT_PARAMETER_TERM =
sig
  structure Sig : ABT_PARAMETER

  datatype 'a term =
     VAR of 'a
   | APP of 'a term Sig.t

  include MONAD where type 'a t = 'a term

  val eq : ('a * 'a -> bool) -> 'a t * 'a t -> bool
  val toString : ('a -> string) -> 'a t -> string

  val collectSubterms : 'a Sig.t -> 'a list
end


