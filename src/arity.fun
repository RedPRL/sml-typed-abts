functor Arity (V : VALENCE) : ARITY =
struct
  structure Valence = V and Sort = V.Sort

  type valence = Valence.t
  type sort = Valence.sort
  type 'a spine = 'a V.spine
  type t = valence spine * sort

  fun eq ((valences, sigma), (valences', sigma')) =
    V.Spine.Pair.allEq V.eq (valences, valences')
      andalso Sort.eq (sigma, sigma')

  fun toString (valences, sigma) =
      let
        val valences' = V.Spine.pretty V.toString ", " valences
        val sigma' = Sort.toString sigma
      in
        "(" ^ valences' ^ ")" ^ sigma'
      end
end

functor ListArity (S : SORT) : ARITY =
  Arity
    (Valence
      (structure Sort = S
       structure Spine = ListSpine))
