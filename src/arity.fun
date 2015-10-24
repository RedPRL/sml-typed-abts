functor Arity (structure Sort : SORT and Spine : SPINE) : ARITY =
struct
  structure Sort = Sort
  structure Valence = Valence (structure Sort = Sort and Spine = Spine)

  type valence = Valence.t
  type t = valence Spine.t * Sort.t

  structure Eq =
  struct
    type t = t
    fun eq ((valences, sigma), (valences', sigma')) =
      Spine.Pair.allEq Valence.Eq.eq (valences, valences')
        andalso Sort.Eq.eq (sigma, sigma')
  end

  structure Show =
  struct
    type t = t
    fun toString (valences, sigma) =
        let
          val valences' = Spine.pretty Valence.Show.toString ", " valences
          val sigma' = Sort.Show.toString sigma
        in
          "(" ^ valences' ^ ")" ^ sigma'
        end
  end
end


