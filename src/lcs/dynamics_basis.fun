functor LcsDynamicsBasisKit (L : LCS_LANGUAGE) =
struct
  structure LcsO = LcsOperator (L)
  structure O = LcsO
  structure Abt = SimpleAbt (O)
  structure Cl = LcsClosure (Abt)

  structure Sig = LcsSignature (structure L = L and Abt = Abt)

  structure M = LcsMachine
    (structure Cl = Cl
     open Abt infix $
     fun isFinal m =
       case out m of
          LcsO.RET _ $ _ => true
        | _ => false)

  datatype 'o pat = `$ of 'o * M.expr M.Cl.Abt.bview list

  type vpat = M.Cl.Abt.symbol O.L.V.t pat
  type kpat = M.Cl.Abt.symbol O.L.K.t pat
end
