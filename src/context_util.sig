signature CONTEXT_UTIL =
sig
  type t
  type key
  type elem

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

  exception MergeFailure
end
