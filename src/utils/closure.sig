signature ABT_CLOSURE =
sig
  structure Abt : ABT

  type 'a env = {params : Abt.symenv, terms : 'a Abt.Var.Ctx.dict}
  type ('a, 'b) tensor = 'a * 'b env

  datatype ('a, 'b) closure = <: of ('a, ('b, 'b) closure) tensor

  val force : (Abt.abt, Abt.abt) closure -> Abt.abt
end
