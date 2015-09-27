functor Arity (Sort : SORT) : ARITY =
struct
  structure Sort = Sort
  structure Valence = Valence (Sort)
  structure Spine = ListSpine

  type valence = Sort.t list * Sort.t
  type arity = valence list * Sort.t
  type t = arity

  fun eq ((valences, sigma), (valences', sigma')) =
    ListPair.allEq Valence.eq (valences, valences')
      andalso Sort.eq (sigma, sigma')

  fun toString ([], sigma) = Sort.toString sigma
    | toString (valences, sigma) =
      let
        val valences' = ListPretty.pretty Valence.toString (", ", valences)
        val sigma' = Sort.toString sigma
      in
        "(" ^ valences' ^ ")" ^ sigma'
      end
end


