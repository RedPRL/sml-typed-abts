signature OPERATOR =
sig
  structure Arity : ARITY

  type 'i t

  val arity : 'i t -> Arity.t
  val support : 'i t -> ('i * Arity.Valence.sort) list

  structure Eq : EQ1 where type 'i t = 'i t
  structure Show : SHOW1 where type 'i t = 'i t
  structure Presheaf : FUNCTOR where type 'i t = 'i t
end

