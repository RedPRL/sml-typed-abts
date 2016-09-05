structure AbtEmptySort :> ABT_SORT =
struct
  datatype t = ROLL of t

  fun eq _ = raise Match
  fun toString _ = raise Match
end
