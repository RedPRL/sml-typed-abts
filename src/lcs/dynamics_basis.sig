signature LCS_DYNAMICS_BASIS =
sig
  structure O : LCS_OPERATOR
  structure M : LCS_MACHINE
    where type 'a Cl.Abt.O.Ar.Vl.Sp.t = 'a list

  structure Sig : LCS_SIGNATURE
    where type valence = O.L.V.Ar.Vl.t

  sharing type Sig.symbol = M.Cl.Abt.Sym.t
  sharing type Sig.metavariable = M.Cl.Abt.Metavar.t
  sharing type Sig.sort = O.L.V.Ar.Vl.S.t
  sharing type Sig.term = M.Cl.Abt.abt
  sharing type M.Cl.Abt.O.Ar.Vl.S.t = O.S.t
  sharing type O.operator = M.Cl.Abt.O.t

  datatype 'o pat = `$ of 'o * M.expr M.Cl.Abt.bview list

  type vpat = M.Cl.Abt.symbol O.L.V.t pat
  type kpat = M.Cl.Abt.symbol O.L.K.t pat

  val plug : Sig.t -> (vpat * kpat) M.Cl.closure -> M.stack -> M.expr M.state
end
