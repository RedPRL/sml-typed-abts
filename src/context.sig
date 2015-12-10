signature METACONTEXT =
sig
  type t
  type metavariable
  type valence

  val isEmpty : t -> bool
  val toList : t -> (metavariable * valence) list

  val empty : t
  val extend : t -> metavariable * valence -> t
  val union : t * t -> t

  val lookup : t -> metavariable -> valence
  val find : t -> metavariable -> valence option

  exception MetavariableNotFound
  exception MergeFailure
end
