functor Arity (structure Sort : SORT and Spine : SPINE) : ARITY =
struct
  structure Sort = Sort
  structure Valence = Valence (structure Sort = Sort and Spine = Spine)

  type valence = Valence.t
  type arity = valence Spine.t * Sort.t
  type t = arity

  fun eq ((valences, sigma), (valences', sigma')) =
    Spine.Pair.allEq Valence.eq (valences, valences')
      andalso Sort.eq (sigma, sigma')

  fun toString (valences, sigma) =
      let
        val valences' = Spine.pretty Valence.toString ", " valences
        val sigma' = Sort.toString sigma
      in
        "(" ^ valences' ^ ")" ^ sigma'
      end
end


