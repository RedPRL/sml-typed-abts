functor AbtValence (structure Sort : ABT_SORT and Sp : SPINE) : ABT_VALENCE =
struct
  structure Sort = Sort and Sp = Sp
  type sort = Sort.t
  type 'a spine = 'a Sp.t
  type bindings = sort spine * sort spine
  type t = bindings * sort

  fun eq (((symbolSorts, variableSorts), sigma), ((symbolSorts', variableSorts'), sigma')) =
    Sp.Pair.allEq Sort.eq (symbolSorts, symbolSorts')
      andalso Sp.Pair.allEq Sort.eq (variableSorts, variableSorts')
      andalso Sort.eq (sigma, sigma')

  fun toString ((symbolSorts,variableSorts), sigma) =
    let
      val symbols' = Sp.pretty Sort.toString ", " symbolSorts
      val variables' = Sp.pretty Sort.toString ", " variableSorts
      val sigma' = Sort.toString sigma
    in
      "{" ^ symbols' ^ "}(" ^ variables' ^ ")." ^ sigma'
    end
end

structure UnisortedAbtValence :> UNISORTED_ABT_VALENCE =
struct
  local
    structure Sort =
    struct
      type t = unit
      fun eq _ = true
      fun toString _ = "_"
    end

    structure Valence = AbtValence (structure Sort = Sort and Sp = ListSpine)
  in
    open Valence
  end

  fun repeat n =
    List.tabulate (n, fn _ => ())

  fun make (i, j) =
    ((repeat i, repeat j), ())
end
