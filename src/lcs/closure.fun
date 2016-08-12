functor LcsClosure (Abt : ABT) : LCS_CLOSURE =
struct

  structure Abt = Abt

  type 'a metaenv = 'a Abt.Metavar.Ctx.dict
  type 'a varenv = 'a Abt.Var.Ctx.dict
  type symenv = Abt.symbol Abt.param Abt.Sym.Ctx.dict

  datatype 'a closure =
    <: of 'a * env
  withtype env = Abt.abs closure metaenv * symenv * Abt.abt closure varenv

  infix <:

  fun map f (m <: rho) = f m <: rho

  fun force (m <: (mrho, srho, rho)) =
    let
      val mrho' = Abt.Metavar.Ctx.map forceB mrho
      val rho' = Abt.Var.Ctx.map force rho
    in
      Abt.renameEnv srho (Abt.substEnv rho' (Abt.metasubstEnv mrho' m))
    end
  and forceB (e <: env) =
    Abt.mapAbs (fn m => force (m <: env)) e

  structure ShowAbt = PlainShowAbt (Abt)

  local
    open Abt
  in
    val emptyEnv =
      (Metavar.Ctx.empty,
       Sym.Ctx.empty,
       Var.Ctx.empty)

    fun envIsEmpty (mrho, srho, vrho) =
      Metavar.Ctx.isEmpty mrho
        andalso Sym.Ctx.isEmpty srho
        andalso Var.Ctx.isEmpty vrho
  end

  fun toStringAbt (m <: env : Abt.abt closure) : string =
    ShowAbt.toString m
      ^ (if envIsEmpty env then "" else " <: " ^ envToString env)

  and toStringAbs (e <: env : Abt.abs closure) : string =
    ShowAbt.toStringAbs e
      ^ (if envIsEmpty env then "" else " <: " ^ envToString env)

  and envToString (mrho, srho, vrho) =
    let
      open Abt
      fun showMetaVarAssign (x, e) =
        Metavar.toString x ^ " ~> " ^ toStringAbs e
      fun showSymAssign (u, p) =
        Sym.toString u ^ " ~> " ^ O.P.toString Sym.toString p
      fun showVarAssign (x, m) =
        Var.toString x ^ " ~> " ^ toStringAbt m

      val slots =
        List.map showMetaVarAssign (Metavar.Ctx.toList mrho)
          @ List.map showSymAssign (Sym.Ctx.toList srho)
          @ List.map showVarAssign (Var.Ctx.toList vrho)
    in
      "{" ^ ListSpine.pretty (fn x => x) ", " slots ^ "}"
    end

  val toString =
    toStringAbt

  fun new x =
    x <: emptyEnv

end
