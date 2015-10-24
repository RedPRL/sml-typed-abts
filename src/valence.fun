functor Valence (structure Sort : SORT and Spine : SPINE) : VALENCE =
struct
  type sort = Sort.t
  structure Spine = Spine
  type bindings = sort Spine.t * sort Spine.t
  type t = bindings * sort

  structure Eq =
  struct
    type t = t
    fun eq (((symbolSorts, variableSorts), sigma), ((symbolSorts', variableSorts'), sigma')) =
      Spine.Pair.allEq Sort.Eq.eq (symbolSorts, symbolSorts')
        andalso Spine.Pair.allEq Sort.Eq.eq (variableSorts, variableSorts')
        andalso Sort.Eq.eq (sigma, sigma')
  end

  structure Show =
  struct
    type t = t
    fun toString ((symbolSorts,variableSorts), sigma) =
      let
        val symbols' = Spine.pretty Sort.Show.toString ", " symbolSorts
        val variables' = Spine.pretty Sort.Show.toString ", " variableSorts
        val sigma' = Sort.Show.toString sigma
      in
        "{" ^ symbols' ^ "}(" ^ variables' ^ ")" ^ sigma'
      end
  end
end


