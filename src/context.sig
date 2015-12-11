signature METACONTEXT =
sig
  type t
  type metavariable
  type valence

  val isEmpty : t -> bool
  val toList : t -> (metavariable * valence) list

  val empty : t

  (* raises MergeFailure if the variable is already present with an incompatible
   * valence *)
  val extend : t -> metavariable * valence -> t

  (* raises MergeFailure if the variable is already present *)
  val extendUnique : t -> metavariable * valence -> t

  (* raises MergeFailure if variables are already present with incompatible
   * valences *)
  val union : t * t -> t

  (* raises MergeFailure if variables are already present *)
  val concat: t * t -> t

  val lookup : t -> metavariable -> valence
  val find : t -> metavariable -> valence option

  exception MetavariableNotFound
  exception MergeFailure
end
