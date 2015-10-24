(* An arity-indexed family of operators *)
signature OPERATOR =
sig
  structure Arity : ARITY

  type t

  structure Eq : EQ where type t = t
  structure Show : SHOW where type t = t

  val arity : t -> Arity.t
end
