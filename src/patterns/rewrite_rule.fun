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

  (* a rewrite rule is valid in case the definiens is well-formed under
   * metavariable context induced by the definiendum *)
  fun into (p ~> m) =
    let
      val (_, Theta) = Pattern.out p
      val Gamma = Abt.varctx m
    in
      if Abt.VarCtx.isEmpty Gamma then
        RULE (p ~> Abt.check Theta (Abt.infer m))
      else
        raise InvalidRule
    end

  fun out (RULE r) = r

  exception RuleInapplicable

  local
    open Abt
    infix $ $# \
    structure Valence = Operator.Arity.Valence
    structure Spine = Valence.Spine
    structure Sort = Valence.Sort

    (* we recursively wring out all the metavariables by looking them up in the
     * environment. Another option would be to replace the environment by a
     * tree of metavariable substitutions, and apply them from the leaves down
     * in order. *)
    fun applyEnv env m =
      let
        val Theta = Abt.metactx m
      in
        if MetaCtx.isEmpty Theta then
          m
        else
          foldl (substMetavar Theta env) m (MetaCtx.toList Theta)
      end
    and substMetavar Theta env ((mv, vl), m) =
      let
        val (xs, us) \ m' = Env.lookup env mv
        val e = Abt.checkb Theta ((xs, us) \ applyEnv env m', vl)
      in
        Abt.metasubst (e, mv) m
      end

    fun applyRen rho m =
      Ren.foldl (fn (u, v, m') => Abt.rename (u, v) m') m rho

  in
    fun compile (RULE (pat ~> m)) n =
      let
        val (rho, env) = unify (pat <*> n)
      in
        applyRen rho (applyEnv env m)
      end
  end
end
