functor AbtValence (structure S : ABT_SORT) : ABT_VALENCE =
struct
  structure S = S
  type sort = S.t
  type 'a spine = 'a list
  type bindings = sort spine
  type t = bindings * sort

  fun eq ((variableSorts, sigma), (variableSorts', sigma')) =
    ListPair.allEq S.eq (variableSorts, variableSorts')
      andalso S.eq (sigma, sigma')

  fun toString (variableSorts, sigma) =
    let
      val variables' = ListSpine.pretty S.toString ", " variableSorts
      val sigma' = S.toString sigma
    in
      "[" ^ variables' ^ "]." ^ sigma'
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

  fun make i =
    (repeat i, ())
end
