functor LcsDynamicsBasisKit (L : LCS_LANGUAGE) =
struct
  structure LcsO = LcsOperator (L)
  structure O = LcsO
  structure Abt = SimpleAbt (O)
  structure Cl = LcsClosure (Abt)

  structure Sig = LcsSignature (structure L = L and Abt = Abt)

  structure M = LcsMachine
    (structure Cl = Cl
     open Cl Abt infix $ $# \ <:

     fun isNeutral (r <: (env as (mrho, srho, vrho))) =
       case out r of
          `x => not (Abt.Var.Ctx.member vrho x)
        | x $# _ => not (Abt.Metavar.Ctx.member mrho x)
        | LcsO.CUT _ $ [_, _ \ r'] => isNeutral (r' <: env)
        | _ => false

     fun isFinal (m <: env) =
       case out m of
          LcsO.RET _ $ _ => true
        | _ => isNeutral (m <: env))

  datatype 'o pat = `$ of 'o * M.expr M.Cl.Abt.bview list

  type vpat = M.Cl.Abt.symbol O.L.V.t pat
  type kpat = M.Cl.Abt.symbol O.L.K.t pat
end
