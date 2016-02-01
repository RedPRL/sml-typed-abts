signature ABT_LINEAR_UNIFICATION =
sig
  include ABT_PATTERN

  (* When [pat] is a pattern and [m] is a closed term without metavariables,
   * then [pat <*> m] is the judgment that [m] unifies with the pattern [pat] *)
  datatype match = <*> of Pattern.pattern * Abt.abt

  exception UnificationFailure
  val unify : match -> Abt.symenv * Abt.metaenv
end

