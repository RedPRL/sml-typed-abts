functor Valence (structure Sort : SORT and Spine : SPINE) : VALENCE =
struct
  type sort = Sort.t
  structure Spine = Spine
  type t = sort Spine.t * sort

  structure Eq =
  struct
    type t = t
    fun eq ((sorts, sigma), (sorts', sigma')) =
      Spine.Pair.allEq Sort.Eq.eq (sorts, sorts')
        andalso Sort.Eq.eq (sigma, sigma')
  end

  structure Show =
  struct
    type t = t
    fun toString (sorts, sigma) =
      let
        val sorts' = Spine.pretty Sort.Show.toString ", " sorts
        val sigma' = Sort.Show.toString sigma
      in
        "(" ^ sorts' ^ ")" ^ sigma'
      end
  end
end


