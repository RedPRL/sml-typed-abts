signature UNORDERED_CONTEXT =
sig
  type t
  type key
  type elem

  val isEmpty : t -> bool
  val toList : t -> (key * elem) list

  val empty : t

  (* raises MergeFailure if the variable is already present with an incompatible
   * valence *)
  val extend : t -> key * elem -> t

  (* raises MergeFailure if the variable is already present *)
  val extendUnique : t -> key * elem -> t

  (* raises MergeFailure if variables are already present with incompatible
   * valences *)
  val union : t * t -> t

  (* raises MergeFailure if variables are already present *)
  val concat: t * t -> t

  val lookup : t -> key -> elem
  val find : t -> key -> elem option

  exception KeyNotFound
  exception MergeFailure
end
