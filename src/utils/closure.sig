signature ABT_CLOSURE =
sig
  structure Abt : ABT

  type 'a env = {params : Abt.symenv, terms : 'a Abt.Var.Ctx.dict}

  (* the tensor product of term presheaves; this is a left Kan extension. *)
  type ('a, 'b) tensor = 'a * 'b env

  (* "closures" are a recursive application of the tensor construction;
     the usual notion of a closure is ('a, 'a) closure. *)
  datatype ('a, 'b) closure = <: of ('a, ('b, 'b) closure) tensor

  val force : (Abt.abt, Abt.abt) closure -> Abt.abt
end

signature ABT_CLOSURE_UTIL =
sig
  include ABT_CLOSURE

  val insertSym : 'a env -> Abt.symbol -> Abt.param -> 'a env
  val insertVar : 'a env -> Abt.variable -> 'a -> 'a env
end
