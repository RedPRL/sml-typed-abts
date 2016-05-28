signature OPERATOR =
sig
  structure Arity : ARITY

  type 'i t

  val arity : 'i t -> Arity.t
  val support : 'i t -> ('i * Arity.Valence.sort) list

  val eq : ('i * 'i -> bool) -> 'i t * 'i t -> bool
  val toString : ('i -> string) -> 'i t -> string
  val map : ('i -> 'j) -> 'i t -> 'j t
end

signature SIMPLE_OPERATOR =
sig
  structure Arity : ARITY

  type t
  val arity : t -> Arity.t
  val eq : t * t -> bool
  val toString : t -> string
end
