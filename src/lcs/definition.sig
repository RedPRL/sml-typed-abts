signature LCS_DEFINTION =
sig
  structure O : LCS_OPERATOR
  structure P : LCS_PATTERN

  type ('s, 'v, 't) value = ('s, 'v, 's O.Val.t, 't) P.pat
  type ('s, 'v, 't) cont = ('s, 'v, 's O.Cont.t, 't) P.pat

  val plug : ('s, 'v, 't) cont -> ('s, 'v, 't) value -> ('s, 'v, 't) P.closure
end
