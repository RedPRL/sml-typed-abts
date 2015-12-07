functor Metacontext
  (structure Metavariable : SYMBOL
   type valence) :> METACONTEXT where type metavariable = Metavariable.t and type valence = valence =
struct
  type metavariable = Metavariable.t
  type valence = valence
  type t = metavariable -> valence

  exception MetavariableNotFound

  fun empty _ = raise MetavariableNotFound
  fun extend Omega (m, v) m'=
    if Metavariable.Eq.eq (m, m') then
      v
    else
      Omega m'

  fun lookup Omega = Omega
end
