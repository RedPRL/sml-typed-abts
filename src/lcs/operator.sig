signature LCS_OPERATOR =
sig
  structure S : LCS_SORT

  structure L : LCS_LANGUAGE
  sharing type L.V.Ar.Vl.S.t = S.AtomicSort.t
  sharing type L.K.Ar.Vl.S.t = S.AtomicSort.t

  type sort = S.t
  type valence = (sort list * sort list) * sort
  type arity = valence list * sort

  datatype 'i operator =
     V of 'i L.V.t (* values *)
   | K of 'i L.K.t (* continuations *)
   | D of 'i L.D.t (* definitional extensions *)
   | RET of S.atomic (* canonical express *)
   | CUT of (S.atomic list * S.atomic) * S.atomic (* cut expression / application of a continuation *)
   | ESUBST of ('i * S.atomic) list * S.atomic list * S.atomic (* explicit substitution of variables & renaming symbols *)
   | CUSTOM of 'i * ('i * S.atomic) list * L.V.Ar.t

  include ABT_OPERATOR
    where type 'i t = 'i operator
    where type 'a Ar.Vl.Sp.t = 'a list
    where type Ar.Vl.S.t = S.t
end
