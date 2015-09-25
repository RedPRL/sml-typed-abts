functor Valence (Sort : SORT) : VALENCE =
struct
  type sort = Sort.t
  type valence = sort list * sort
  type t = valence

  fun eq ((sorts, sigma), (sorts', sigma')) =
    ListPair.allEq Sort.eq (sorts, sorts')
      andalso Sort.eq (sigma, sigma')

  fun toString ([], sigma) = Sort.toString sigma
    | toString (sorts, sigma) =
      let
        val sorts' = ListPretty.pretty Sort.toString (", ", sorts)
        val sigma' = Sort.toString sigma
      in
        "(" ^ sorts' ^ ")" ^ sigma'
      end
end


