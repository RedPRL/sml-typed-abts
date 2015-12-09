signature METACONTEXT =
sig
  type t
  type metavariable
  type valence

  val empty : t

  val isEmpty : t -> bool
  val toList : t -> (metavariable * valence) list

  exception NameClash

  (* raises NameClash *)
  val extend : t -> metavariable * valence -> t

  (* raises NameClash *)
  val concat : t * t -> t

  (* raises NameClash if the name is already present with a different valence *)
  val updateMonotonic : t -> metavariable * valence -> t
  val union : t * t -> t

  exception MetavariableNotFound

  (* raises MetavariableNotFound *)
  val lookup : t -> metavariable -> valence

  val find : t -> metavariable -> valence option
end
