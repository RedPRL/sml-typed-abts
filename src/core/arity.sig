(* An arity is the "type" that the underlying framework of ABTs assigns
 * to operators. It contains two parts
 *
 *  - The actual sort that the operator belongs to when it's fully applied.
 *  - The valence (sorts of bound symbols + sorts of bound variables + sort of term)
 *    of each subterm of the operator
 *
 * An operator is fully determined by its name + arity
 *)
signature ABT_ARITY =
sig
  structure Vl : ABT_VALENCE

  type valence = Vl.t
  type sort = Vl.sort
  type psort = Vl.psort
  type 'a spine = 'a Vl.spine

  type t = valence spine * sort
  val toString : t -> string
  val eq : t * t -> bool
end

signature UNISORTED_ABT_ARITY =
sig
  include ABT_ARITY
    where type Vl.S.t = unit
    where type 'a Vl.Sp.t = 'a list

  val make : (int * int) list -> t
end
