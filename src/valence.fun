functor Valence (structure Sort : SORT and Spine : SPINE) : VALENCE =
struct
  type sort = Sort.t
  structure Spine = Spine
  type valence = sort Spine.t * sort
  type t = valence

  fun eq ((sorts, sigma), (sorts', sigma')) =
    Spine.Pair.allEq Sort.eq (sorts, sorts')
      andalso Sort.eq (sigma, sigma')

  fun toString (sorts, sigma) =
      let
        val sorts' = Spine.pretty Sort.toString ", " sorts
        val sigma' = Sort.toString sigma
      in
        "(" ^ sorts' ^ ")" ^ sigma'
      end
end


