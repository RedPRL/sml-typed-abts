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
    <: of 'a * (Abt.abs closure metaenv * symenv * Abt.abt closure varenv)

  infix <:

  fun map f (m <: rho) = f m <: rho

  val emptyEnv =
    (Abt.Metavariable.Ctx.empty,
     Abt.Symbol.Ctx.empty,
     Abt.Variable.Ctx.empty)

  fun new x =
    x <: emptyEnv

  fun force (m <: (mrho, srho, rho)) =
    let
      val mrho' = Abt.Metavariable.Ctx.map forceB mrho
      val rho' = Abt.Variable.Ctx.map force rho
    in
      Abt.renameEnv srho (Abt.substEnv rho' (Abt.metasubstEnv mrho' m))
    end
  and forceB (e <: env) =
    Abt.mapAbs (fn m => force (m <: env)) e

  structure ShowAbt = DebugShowAbt (Abt)
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

end
