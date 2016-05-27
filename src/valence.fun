functor Valence (structure Sort : SORT and Spine : SPINE) : VALENCE =
struct
  structure Sort = Sort and Spine = Spine
  type sort = Sort.t
  type 'a spine = 'a Spine.t
  type bindings = sort spine * sort spine
  type t = bindings * sort

  fun eq (((symbolSorts, variableSorts), sigma), ((symbolSorts', variableSorts'), sigma')) =
    Spine.Pair.allEq Sort.eq (symbolSorts, symbolSorts')
      andalso Spine.Pair.allEq Sort.eq (variableSorts, variableSorts')
      andalso Sort.eq (sigma, sigma')

  fun toString ((symbolSorts,variableSorts), sigma) =
    let
      val symbols' = Spine.pretty Sort.toString ", " symbolSorts
      val variables' = Spine.pretty Sort.toString ", " variableSorts
      val sigma' = Sort.toString sigma
    in
      "{" ^ symbols' ^ "}(" ^ variables' ^ ")." ^ sigma'
    end
end

structure UnisortedValence :> UNISORTED_VALENCE =
struct
  local
    structure Sort =
    struct
      type t = unit
      fun eq _ = true
      fun toString _ = "_"
    end

    structure Valence = Valence (structure Sort = Sort and Spine = ListSpine)
  in
    open Valence
  end

  fun repeat n =
    List.tabulate (n, fn _ => ())

  fun make (i, j) =
    ((repeat i, repeat j), ())
end
