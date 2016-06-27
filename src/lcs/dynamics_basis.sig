signature LCS_DYNAMICS_BASIS =
sig
  structure O : LCS_OPERATOR
  structure M : LCS_MACHINE
    where type 'a Cl.Abt.O.Ar.Vl.Sp.t = 'a list
    where type 'a K.t = 'a O.L.K.t

  structure Sig : LCS_SIGNATURE
    where type valence = O.L.V.Ar.Vl.t

  sharing type Sig.symbol = M.Cl.Abt.Sym.t
  sharing type Sig.metavariable = M.Cl.Abt.Metavar.t
  sharing type Sig.sort = O.L.V.Ar.Vl.S.t
  sharing type Sig.term = M.Cl.Abt.abt
  sharing type M.Cl.Abt.O.Ar.Vl.S.t = O.S.t
  sharing type O.operator = M.Cl.Abt.O.t

  type vpat = (M.Cl.Abt.symbol O.L.V.t, M.expr) M.pat
  type kpat = (M.Cl.Abt.symbol O.L.K.t, M.expr M.Cl.closure) M.pat
  type dpat = (M.Cl.Abt.symbol O.L.D.t, M.expr) M.pat

  val plug : Sig.t -> vpat M.Cl.closure * kpat -> M.stack -> M.expr M.state

  val catch : Sig.t -> vpat M.Cl.closure * kpat -> M.stack -> M.expr M.state option

  (* Delta expansion / expansion of definitional extensions *)
  val delta : Sig.t -> dpat M.Cl.closure -> M.expr M.Cl.closure
end
