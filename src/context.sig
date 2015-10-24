signature METACONTEXT =
sig
  type t
  type metavariable
  type valence

  val empty : t
  val extend : t -> metavariable * valence -> t

  val lookup : t -> metavariable -> valence
  exception MetavariableNotFound
end
