signature LCS_OPERATOR =
sig
  structure Sort : LCS_SORT

  structure L : LCS_LANGUAGE
  sharing type L.V.Ar.Vl.Sort.t = Sort.AtomicSort.t
  sharing type L.K.Ar.Vl.Sort.t = Sort.AtomicSort.t

  type sort = Sort.t
  type valence = (sort list * sort list) * sort
  type arity = valence list * sort

  datatype 'i operator =
     V of 'i L.V.t
   | K of 'i L.K.t
   | RET of Sort.atomic
   | CUT of Sort.atomic * Sort.atomic
   | CUSTOM of 'i * ('i * Sort.atomic) list * L.V.Ar.t

  include ABT_OPERATOR
    where type 'i t = 'i operator
    where type 'a Ar.Vl.Spine.t = 'a list
    where type Ar.Vl.Sort.t = Sort.t
end
