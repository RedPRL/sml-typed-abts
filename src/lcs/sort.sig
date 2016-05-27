signature LCS_SORT =
sig
  structure AtomicSort : SORT

  type atomic = AtomicSort.t

  datatype t =
      VAL of atomic
    | CONT of atomic * atomic
    | CMD of atomic

  val eq : t * t -> bool
  val toString : t -> string
end
