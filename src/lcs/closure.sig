signature LCS_CLOSURE =
sig
  structure Abt : ABT

  type 'a metaenv = 'a Abt.Metavar.Ctx.dict
  type 'a varenv = 'a Abt.Var.Ctx.dict
  type symenv = Abt.symbol Abt.param Abt.Sym.Ctx.dict

  datatype 'a closure =
    <: of 'a * (Abt.abs closure metaenv * symenv * Abt.abt closure varenv)

  type env = Abt.abs closure metaenv * symenv * Abt.abt closure varenv

  val new : 'a -> 'a closure
  val force : Abt.abt closure -> Abt.abt
  val map : ('a -> 'b) -> 'a closure -> 'b closure

  val toString : Abt.abt closure -> string
end
