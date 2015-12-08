signature METACONTEXT =
sig
  type t
  type metavariable
  type valence

  val empty : t

  exception NameClash

  (* raises NameClash *)
  val extend : t -> metavariable * valence -> t

  (* raises NameClash *)
  val concat : t * t -> t

  exception MetavariableNotFound

  (* raises MetavariableNotFound *)
  val lookup : t -> metavariable -> valence

  val find : t -> metavariable -> valence option
end
