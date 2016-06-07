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

  structure MetaCtxUtil = ContextUtil (structure Ctx = Abt.Metavar.Ctx and Elem = Abt.O.Ar.Vl)

  fun subctx psi1 psi2 =
    Abt.Metavar.Ctx.foldl
      (fn (x, vl, r) =>
         Abt.O.Ar.Vl.eq (vl, Abt.Metavar.Ctx.lookup psi2 x)
           handle _ => false)
      true
      psi1

  (* a rewrite rule is valid in case the definiens is well-formed under
   * metavariable context induced by the definiendum *)
  fun into (p ~> m) =
    let
      val (_, psi) = Pattern.out p
      val psi' = Abt.metactx m
      val gamma = Abt.varctx m
    in
      if Abt.Var.Ctx.isEmpty gamma andalso subctx psi' psi then
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
