functor AbtArity (Vl : ABT_VALENCE) : ABT_ARITY =
struct
  structure Vl = Vl and Sort = Vl.Sort

  type valence = Vl.t
  type sort = Vl.sort
  type 'a spine = 'a Vl.spine
  type t = valence spine * sort

  fun eq ((valences, sigma), (valences', sigma')) =
    Vl.Sp.Pair.allEq Vl.eq (valences, valences')
      andalso Sort.eq (sigma, sigma')

  fun toString (valences, sigma) =
      let
        val valences' = Vl.Sp.pretty Vl.toString ", " valences
        val sigma' = Sort.toString sigma
      in
        "(" ^ valences' ^ ")" ^ sigma'
      end
end

functor ListAbtArity (S : ABT_SORT) : ABT_ARITY =
  AbtArity
    (AbtValence
      (structure Sort = S and Sp = ListSpine))

structure UnisortedAbtArity : UNISORTED_ABT_ARITY =
struct
  local
    structure Vl = UnisortedAbtValence
    structure A = AbtArity (Vl)
  in
    fun make vls =
      (List.map Vl.make vls, ())
    open A
  end
end
