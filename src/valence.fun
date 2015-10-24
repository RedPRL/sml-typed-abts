functor Valence (structure Sort : SORT and Spine : SPINE) : VALENCE =
struct
  type sort = Sort.t
  structure Spine = Spine
  type bindings =
    {symbols : sort Spine.t,
     variables : sort Spine.t}
  type t = bindings * sort

  structure Eq =
  struct
    type t = t
    fun eq ((bindings : bindings, sigma), (bindings' : bindings, sigma')) =
      Spine.Pair.allEq Sort.Eq.eq (#symbols bindings, #symbols bindings')
        andalso Spine.Pair.allEq Sort.Eq.eq (#variables bindings, #variables bindings')
        andalso Sort.Eq.eq (sigma, sigma')
  end

  structure Show =
  struct
    type t = t
    fun toString ({symbols,variables}, sigma) =
      let
        val symbols' = Spine.pretty Sort.Show.toString ", " symbols
        val variables' = Spine.pretty Sort.Show.toString ", " variables
        val sigma' = Sort.Show.toString sigma
      in
        "{" ^ symbols' ^ "}(" ^ variables' ^ ")" ^ sigma'
      end
  end
end


