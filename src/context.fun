functor Metacontext
  (structure Metavariable : SYMBOL
   structure Valence : EQ) :> METACONTEXT where type metavariable = Metavariable.t and type valence = Valence.t =
struct
  type metavariable = Metavariable.t
  type valence = Valence.t
  type t = (metavariable * valence) list

  exception MetavariableNotFound
  exception NameClash

  val empty = []

  fun isEmpty [] = true
    | isEmpty _ = false

  fun toList Theta = Theta

  fun fiber m (m', _) =
    Metavariable.Eq.eq (m, m')

  fun find Theta m =
    Option.map #2 (List.find (fiber m) Theta)

  fun lookup Theta m =
    case find Theta m of
         SOME vl => vl
       | NONE => raise MetavariableNotFound

  fun extend Theta (m, vl) =
    case find Theta m of
         SOME _ => raise NameClash
       | NONE => (m, vl) :: Theta

  fun updateMonotonic Theta (m, vl) =
    case find Theta m of
         SOME vl' => if Valence.eq (vl, vl') then Theta else raise NameClash
       | NONE => (m, vl) :: Theta

  fun concat (Theta, Theta') =
    List.foldl
      (fn (h, Theta'') => extend Theta'' h)
      Theta
      Theta'

  fun union (Theta, Theta') =
    List.foldl
      (fn (h, Theta'') => updateMonotonic Theta'' h)
      Theta
      Theta'
end
