(* An arity is the "type" that the underlying framework of ABTs assigns
 * to operators. It contains to parts
 *
 *  - The actual sort that the operator belongs to when it's fully applied.
 *  - The valence (sort of bound symbols + sort of bound variables + sort of term)
 *    of each subterm of the operator
 *
 * An operator is fully determined by its name + arity
 *)
signature ARITY =
sig
  structure Sort : SORT
  structure Valence : VALENCE
  sharing type Valence.sort = Sort.t

  type t = Valence.t Valence.Spine.t * Sort.t
  structure Show : SHOW where type t = t
  structure Eq : EQ where type t = t
end
