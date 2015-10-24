signature OPERATOR =
sig
  structure Arity : ARITY

  type 'i t

  (* not Definition-compliant, but included in Successor ML *)
  functor Eq (I : EQ) : EQ where type t = I.t t
  functor Show (I : SHOW) : SHOW where type t = I.t t

  val proj : 'i t -> ('i * Arity.Valence.sort) list * Arity.t

  structure Renaming : FUNCTOR where type 'i t = 'i t
end

