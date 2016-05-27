signature LCS_OPERATOR =
sig
  structure Sort : LCS_SORT

  structure V : OPERATOR
    where type 'a Arity.Valence.Spine.t = 'a list
  structure K : OPERATOR
    where type 'a Arity.Valence.Spine.t = 'a list

  sharing type V.Arity.Valence.Sort.t = Sort.AtomicSort.t
  sharing type K.Arity.Valence.Sort.t = Sort.AtomicSort.t

  type sort = Sort.t
  type valence = (sort list * sort list) * sort
  type arity = valence list * sort

  datatype 'i operator =
     V of 'i V.t
   | K of 'i K.t
   | RET of Sort.atomic
   | CUT of Sort.atomic * Sort.atomic

  include OPERATOR
    where type 'i t = 'i operator
    where type 'a Arity.Valence.Spine.t = 'a list
    where type Arity.Valence.Sort.t = Sort.t
end
