signature LCS_LANGUAGE =
sig
  (* Values *)
  structure V : ABT_OPERATOR where type 'a Ar.Vl.Sp.t = 'a list

  (* Continuations *)
  structure K : ABT_OPERATOR where type 'a Ar.Vl.Sp.t = 'a list

  (* Definitional Extensions *)
  structure D : ABT_OPERATOR where type 'a Ar.Vl.Sp.t = 'a list

  sharing type V.Ar.Vl.S.t = K.Ar.Vl.S.t
  sharing type V.Ar.Vl.S.t = D.Ar.Vl.S.t

  (* The sort of the principal argument / input to a continuation *)
  val input : 'i K.t -> V.Ar.sort

  (* The sort of symbols that denote custom operator ids *)
  val opidSort : V.Ar.sort option
end
