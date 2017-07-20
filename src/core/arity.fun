functor AbtArity (Vl : ABT_VALENCE) : ABT_ARITY =
struct
  structure Vl = Vl and PS = Vl.PS and S = Vl.S

  type valence = Vl.t
  type sort = Vl.sort
  type psort = Vl.psort
  type 'a spine = 'a Vl.spine
  type t = valence spine * sort

  fun eq ((valences, sigma), (valences', sigma')) =
    ListPair.allEq Vl.eq (valences, valences')
      andalso S.eq (sigma, sigma')

  fun toString (valences, sigma) =
      let
        val valences' = ListSpine.pretty Vl.toString ", " valences
        val sigma' = S.toString sigma
      in
        "(" ^ valences' ^ ")" ^ sigma'
      end
end

functor ListAbtArity (structure S : ABT_SORT and PS : ABT_SORT) : ABT_ARITY =
  AbtArity
    (AbtValence
      (structure S = S and PS = PS and Sp = ListSpine))

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
