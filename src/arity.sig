(* An arity is the "type" that the underlying framework of ABTs assigns
 * to operators. It contains two parts
 *
 *  - The actual sort that the operator belongs to when it's fully applied.
 *  - The valence (sorts of bound symbols + sorts of bound variables + sort of term)
 *    of each subterm of the operator
 *
 * An operator is fully determined by its name + arity
 *)
signature ARITY =
sig
  structure Valence : VALENCE
  type valence = Valence.t
  type sort = Valence.sort
  type 'a spine = 'a Valence.spine

  type t = valence spine * sort
  val toString : t -> string
  val eq : t * t -> bool
end
