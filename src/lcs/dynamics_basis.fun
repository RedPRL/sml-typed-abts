functor LcsDynamicsBasisKit (L : LCS_LANGUAGE) =
struct
  structure O = LcsOperator (L)
  structure Abt = SimpleAbt (O)
  structure Cl = LcsClosure (Abt)

  structure Sig = LcsSignature (structure L = L and Abt = Abt)

  structure M = LcsMachine
    (structure Cl = Cl
     open O Cl Abt infix $ $# \ <:

     fun isNeutral (r <: (env as (mrho, srho, vrho))) =
       case out r of
          `x => not (Abt.Var.Ctx.member vrho x)
        | x $# _ => not (Abt.Metavar.Ctx.member mrho x)
        | CUT _ $ [_, _ \ r'] => isNeutral (r' <: env)
        | _ => false

     fun isFinal (m <: env) =
       case out m of
          RET _ $ _ => true
        | _ => isNeutral (m <: env))

  datatype 'o pat = `$ of 'o * M.expr M.Cl.Abt.bview list

  type vpat = M.Cl.Abt.symbol O.L.V.t pat
  type kpat = M.Cl.Abt.symbol O.L.K.t pat
  type dpat = M.Cl.Abt.symbol O.L.D.t pat

  local
    infix `$ $$ \
    open O Abt
  in
    fun unquoteV (theta `$ es) =
      V theta $$ es

    fun unquoteK (theta `$ es) =
      K theta $$ es
  end
end
