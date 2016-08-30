signature ABT_LINEAR_UNIFICATION =
sig
  include ABT_PATTERN

  (* When [pat] is a pattern and [m] is a closed term without metavariables,
   * then [pat <*> m] is the judgment that [m] unifies with the pattern [pat] *)
  datatype match = <*> of Pattern.pattern * Abt.abt

  exception UnificationFailure

  (* TODO: use symenv, properly unify parameters *)
  val unify : match -> Abt.symbol Abt.Sym.Ctx.dict * Abt.metaenv
end

