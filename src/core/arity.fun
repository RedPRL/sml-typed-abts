functor AbtArity (V : ABT_VALENCE) : ABT_ARITY =
struct
  structure Vl = V and Sort = V.Sort

  type valence = V.t
  type sort =   V.sort
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
    fun make vls =
      (List.map V.make vls, ())
    open A
  end
end
