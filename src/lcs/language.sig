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
  sharing type V.P.t = K.P.t
  sharing type V.P.t = D.P.t

  (* The valence sort of the principal argument / input to a continuation.
     Should return a list of sorts of symbols to bind (which will in most
     cases be empty), and an output sort. *)
  val input : 'i K.t -> V.Ar.sort list * V.Ar.sort

  (* The sort of symbols that denote custom operator ids *)
  val opidSort : V.Ar.sort option
end
