functor Metacontext
  (structure Metavariable : SYMBOL
   type valence) :> METACONTEXT where type metavariable = Metavariable.t and type valence = valence =
struct
  type metavariable = Metavariable.t
  type valence = valence
  type t = (metavariable * valence) list

  exception MetavariableNotFound
  exception NameClash

  val empty = []

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

  fun concat (Theta, Theta') =
    List.foldl
      (fn (h, Theta'') => extend Theta'' h)
      Theta
      Theta'
end
