signature LCS_SORT =
sig
  structure AtomicSort : ABT_SORT

  type atomic = AtomicSort.t

  datatype t =
      VAL of atomic
    | CONT of (atomic list * atomic) * atomic
    | EXP of atomic

  (* Select a sort with which to reflect user-defined operator id symbols *)
  val opidSort : atomic option

  val eq : t * t -> bool
  val toString : t -> string
end
