(* An arity-indexed family of operators *)
signature OPERATOR =
sig
  structure Arity : ARITY

  type operator
  include
    sig
      include EQ
      include SHOW
    end
    where type t = operator

  val arity : operator -> Arity.arity
end

