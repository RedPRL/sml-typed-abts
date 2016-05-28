functor ShowEnv (S : SYMBOL) =
struct
  fun toString (f : 'a -> string) (rho : 'a S.Ctx.dict) =
    let
      val xs = S.Ctx.toList rho
      fun f' (x, e) =
        S.toString x
          ^ " ~> "
          ^ f e
    in
      "[" ^ ListSpine.pretty f' ", " xs ^ "]"
    end
end

functor LcsClosure (Abt : ABT) : LCS_CLOSURE =
struct

  structure Abt = Abt

  type 'a metaenv = 'a Abt.Metavariable.Ctx.dict
  type 'a varenv = 'a Abt.Variable.Ctx.dict
  type symenv = Abt.symbol Abt.Symbol.Ctx.dict

  datatype 'a closure =
    <: of 'a * env
  withtype env = Abt.abs closure metaenv * symenv * Abt.abt closure varenv

  infix <:

  fun map f (m <: rho) = f m <: rho

  fun force (m <: (mrho, srho, rho)) =
    let
      val mrho' = Abt.Metavariable.Ctx.map forceB mrho
      val rho' = Abt.Variable.Ctx.map force rho
    in
      Abt.renameEnv srho (Abt.substEnv rho' (Abt.metasubstEnv mrho' m))
    end
  and forceB (e <: env) =
    Abt.mapAbs (fn m => force (m <: env)) e

  structure ShowAbt = PlainShowAbt (Abt)
  structure ShowMetaEnv = ShowEnv (Abt.Metavariable)
  structure ShowSymEnv = ShowEnv (Abt.Symbol)
  structure ShowVarEnv = ShowEnv (Abt.Variable)

  fun toStringAbt (m <: env : Abt.abt closure) : string =
    ShowAbt.toString m ^ " <: " ^ envToString env

  and toStringAbs (e <: env : Abt.abs closure) : string =
    ShowAbt.toStringAbs e ^ " <: " ^ envToString env

  and envToString (mrho, srho, vrho) =
    "("
      ^ ShowMetaEnv.toString toStringAbs mrho
      ^ ", "
      ^ ShowSymEnv.toString Abt.Symbol.toString srho
      ^ ", "
      ^ ShowVarEnv.toString toStringAbt vrho
      ^ ")"

  val toString =
    toStringAbt

  local
    open Abt
  in
    val emptyEnv =
      (Metavariable.Ctx.empty,
       Symbol.Ctx.empty,
       Variable.Ctx.empty)

    fun mergeEnv ((mrho1, srho1, vrho1), (mrho2, srho2, vrho2)) =
      let
        val mrho3 =
          Metavariable.Ctx.union mrho1 mrho2 (fn (k, e1 <: env1, e2 <: env2) =>
            if Abt.eqAbs (e1, e2) then
              e1 <: mergeEnv (env1, env2)
            else
              raise Fail ("Environment merge failure: " ^ ShowAbt.toStringAbs e1 ^ " vs " ^ ShowAbt.toStringAbs e2))

        val srho3 =
          Symbol.Ctx.union srho1 srho2 (fn (k, u, v) =>
            if Symbol.eq (u, v) then
              u
            else
              raise Fail "Environment merge failure")

        val vrho3 =
          Variable.Ctx.union vrho1 vrho2 (fn (k, m1 <: env1, m2 <: env2) =>
            if Abt.eq (m1, m2) then
              m1 <: mergeEnv (env1, env2)
            else
              raise Fail ("Environment merge failure: " ^ ShowAbt.toString m1 ^ " vs " ^ ShowAbt.toString m2))
      in
        (mrho3, srho3, vrho3)
      end
  end

  fun new x =
    x <: emptyEnv

end
