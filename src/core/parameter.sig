(* First order signatures. Probably should rename. *)
signature ABT_PARAMETER =
sig
  include FUNCTOR

  structure Sort : ABT_SORT
  val arity : 'a t -> Sort.t t * Sort.t

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

  (* returns a list of free variables and the sorts at which they are used.
   * It is the responsibility of the client to ensure that these variables
   * are used consistently. *)

  exception SortError
  val check : Sig.Sort.t -> 'a term -> ('a * Sig.Sort.t) list
  val freeVars : 'a term Sig.t -> ('a * Sig.Sort.t) list

  include MONAD where type 'a t = 'a term
  val map : ('a -> 'b) -> 'a term -> 'b term

  val eq : ('a * 'a -> bool) -> 'a t * 'a t -> bool
  val toString : ('a -> string) -> 'a t -> string
  val collectSubterms : 'a Sig.t -> 'a list
end


