signature OPERATOR =
sig
  structure Arity : ARITY

  type 'i t

  val eq : ('i * 'i -> bool) -> 'i t * 'i t -> bool
  val toString : ('i -> string) -> 'i t -> string

  val arity : 'i t -> Arity.t
  val support : 'i t -> ('i * Arity.Valence.sort) list

  structure Presheaf : FUNCTOR where type 'i t = 'i t
end

