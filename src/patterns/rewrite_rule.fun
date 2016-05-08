functor RewriteRule (P : ABT_PATTERN) : REWRITE_RULE =
struct
  open P
  open Pattern

  type term = Abt.abt

  datatype view = ~> of pattern * term
  datatype rule = RULE of view

  structure Unify = AbtLinearUnification (P)
  open Unify

  infix ~> $@ <*>

  exception InvalidRule

  structure MetaCtxUtil = ContextUtil (structure Ctx = Abt.Metavariable.Ctx and Elem = Abt.Operator.Arity.Valence)

  (* a rewrite rule is valid in case the definiens is well-formed under
   * metavariable context induced by the definiendum *)
  fun into (p ~> m) =
    let
      val (_, psi) = Pattern.out p
      val psi' = Abt.metactx m
      (* Ensure that the metacontexts are compatible *)
      val psi'' = MetaCtxUtil.union (psi, psi')
      val gamma = Abt.varctx m
    in
      if Abt.Variable.Ctx.isEmpty gamma then
        RULE (p ~> m)
      else
        raise InvalidRule
    end

  fun out (RULE r) = r

  fun compile (RULE (pat ~> m)) n =
    let
      val (rho, env) = unify (pat <*> n)
    in
      Abt.renameEnv rho (Abt.metasubstEnv env m)
    end
end
