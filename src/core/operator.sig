signature ABT_OPERATOR =
sig
  structure Ar : ABT_ARITY

  type t

  val arity : t -> Ar.t

  val eq : t * t -> bool
  val toString : t -> string
end