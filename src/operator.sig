signature OPERATOR =
sig
  structure Arity : ARITY

  type 'i t

  (* not Definition-compliant, but included in Successor ML *)
  functor Eq (I : EQ) : EQ where type t = I.t t
  functor Show (I : SHOW) : SHOW where type t = I.t t

  val arity : 'i t -> Arity.t
  val support : 'i t -> ('i * Arity.Valence.sort) list

  structure Presheaf : FUNCTOR where type 'i t = 'i t
end

