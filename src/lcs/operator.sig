signature CONT_OPERATOR =
sig
  include OPERATOR
  val input : 'i t -> Arity.Valence.sort
end

signature LCS_OPERATOR =
sig
  structure Sort : LCS_SORT

  structure Val : OPERATOR
  sharing type Val.Arity.Valence.Sort.t = Sort.AtomicSort.t

  structure Cont : CONT_OPERATOR
  sharing type Cont.Arity.Valence.Sort.t = Sort.AtomicSort.t
  sharing type Cont.Arity.Valence.Spine.t = Val.Arity.Valence.Spine.t

  datatype 'i cmd =
     RET of Sort.atomic
   | CUT of Sort.atomic * Sort.atomic

  datatype 'i operator =
     V of 'i Val.t
   | K of 'i Cont.t
   | C of 'i cmd

  include OPERATOR
    where type 'i t = 'i operator
    where type Arity.Valence.Sort.t = Sort.t
    where type 'a Arity.Valence.Spine.t = 'a Val.Arity.Valence.Spine.t
end
