signature CONT_OPERATOR =
sig
  include OPERATOR
  val input : 'i t -> Arity.Valence.sort
end

signature LCS_OPERATOR =
sig
  structure Sort : LCS_SORT

  structure Val : OPERATOR
    where type 'a Arity.Valence.Spine.t = 'a list
  sharing type Val.Arity.Valence.Sort.t = Sort.AtomicSort.t

  structure Cont : CONT_OPERATOR
    where type 'a Arity.Valence.Spine.t = 'a list
  sharing type Cont.Arity.Valence.Sort.t = Sort.AtomicSort.t

  type sort = Sort.t
  type valence = (sort list * sort list) * sort
  type arity = valence list * sort

  datatype 'i operator =
     V of 'i Val.t
   | K of 'i Cont.t
   | RET of Sort.atomic
   | CUT of Sort.atomic * Sort.atomic

  include OPERATOR
    where type 'i t = 'i operator
    where type Arity.Valence.Sort.t = Sort.t
    where type 'a Arity.Valence.Spine.t = 'a list
end
