functor AbtArity (V : ABT_VALENCE) : ABT_ARITY =
struct
  structure Valence = V and Sort = V.Sort

  type valence = Valence.t
  type sort = Valence.sort
  type 'a spine = 'a V.spine
  type t = valence spine * sort

  fun eq ((valences, sigma), (valences', sigma')) =
    V.Spine.Pair.allEq V.eq (valences, valences')
      andalso Sort.eq (sigma, sigma')

  fun toString (valences, sigma) =
      let
        val valences' = V.Spine.pretty V.toString ", " valences
        val sigma' = Sort.toString sigma
      in
        "(" ^ valences' ^ ")" ^ sigma'
      end
end

functor ListAbtArity (S : ABT_SORT) : ABT_ARITY =
  AbtArity
    (AbtValence
      (structure Sort = S
       structure Spine = ListSpine))

structure UnisortedAbtArity : UNISORTED_ABT_ARITY =
struct
  local
    structure V = UnisortedAbtValence
    structure A = AbtArity (V)
  in
    open A

    fun make vls =
      (List.map V.make vls, ())
  end
end
