signature LCS_DYNAMICS_BASIS =
sig
  structure O : LCS_OPERATOR
  structure M : LCS_MACHINE
    where type 'a Cl.Abt.Operator.Ar.Vl.Sp.t = 'a list

  structure Sig : LCS_SIGNATURE
    where type valence = O.L.V.Ar.Vl.t

  sharing type Sig.symbol = M.Cl.Abt.Symbol.t
  sharing type Sig.metavariable = M.Cl.Abt.Metavariable.t
  sharing type Sig.sort = O.L.V.Ar.Vl.Sort.t
  sharing type Sig.term = M.Cl.Abt.abt
  sharing type M.Cl.Abt.Operator.Ar.Vl.Sort.t = O.Sort.t
  sharing type O.operator = M.Cl.Abt.Operator.t

  datatype 'o pat = `$ of 'o * M.expr M.Cl.Abt.bview list

  type vpat = M.Cl.Abt.symbol O.L.V.t pat
  type kpat = M.Cl.Abt.symbol O.L.K.t pat

  val plug : Sig.t -> (vpat * kpat) M.state -> M.expr M.state
end
