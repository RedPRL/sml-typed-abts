functor AbtValence (structure S : ABT_SORT and Sp : SPINE) : ABT_VALENCE =
struct
  structure S = S and Sp = Sp
  type sort = S.t
  type 'a spine = 'a Sp.t
  type bindings = sort spine * sort spine
  type t = bindings * sort

  fun eq (((symbolSorts, variableSorts), sigma), ((symbolSorts', variableSorts'), sigma')) =
    Sp.Pair.allEq S.eq (symbolSorts, symbolSorts')
      andalso Sp.Pair.allEq S.eq (variableSorts, variableSorts')
      andalso S.eq (sigma, sigma')

  fun toString ((symbolSorts,variableSorts), sigma) =
    let
      val symbols' = Sp.pretty S.toString ", " symbolSorts
      val variables' = Sp.pretty S.toString ", " variableSorts
      val sigma' = S.toString sigma
    in
      "{" ^ symbols' ^ "}(" ^ variables' ^ ")." ^ sigma'
    end
end

structure UnisortedAbtValence :> UNISORTED_ABT_VALENCE =
struct
  local
    structure S =
    struct
      type t = unit
      fun eq _ = true
      fun toString _ = "_"
    end

    structure Valence = AbtValence (structure S = S and Sp = ListSpine)
  in
    open Valence
  end

  fun repeat n =
    List.tabulate (n, fn _ => ())

  fun make (i, j) =
    ((repeat i, repeat j), ())
end
