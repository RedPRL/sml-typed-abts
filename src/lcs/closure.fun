functor LcsClosure (Abt : ABT) : LCS_CLOSURE =
struct

  structure Abt = Abt

  type 'a metaenv = 'a Abt.Metavariable.Ctx.dict
  type 'a varenv = 'a Abt.Variable.Ctx.dict
  type symenv = Abt.symbol Abt.Symbol.Ctx.dict

  datatype 'a closure =
    <: of 'a * (Abt.abs closure metaenv * symenv * Abt.abt closure varenv)

  infix <:

  fun map f (m <: rho) = f m <: rho
end
