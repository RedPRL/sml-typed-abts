functor ShowAbt
  (structure Abt : ABT
   structure ShowVar : SHOW where type t = Abt.variable
   structure ShowSym : SHOW where type t = Abt.symbol) :>
sig
  include SHOW where type t = Abt.abt
  val toStringAbs : Abt.abs -> string
end =
struct
  open Abt infix $ $# infixr \
  type t = abt

  structure Sp = Abt.O.Ar.Vl.Sp

  fun toString M =
    case #1 (infer M) of
         `x => ShowVar.toString x
       | theta $ es =>
           if Sp.isEmpty es then
             O.toString (O.P.toString ShowSym.toString) theta
           else
             O.toString (O.P.toString ShowSym.toString) theta
                ^ "(" ^ Sp.pretty toStringB "; " es ^ ")"
       | mv $# (ps, ms) =>
           let
             val ps' = Sp.pretty (O.P.toString ShowSym.toString o #1) "," ps
             val ms' = Sp.pretty toString "," ms
           in
             "#" ^ Abt.Metavar.toString mv
                 ^ (if Sp.isEmpty ps then "" else "{" ^ ps' ^ "}")
                 ^ (if Sp.isEmpty ms then "" else "[" ^ ms' ^ "]")
           end

  and toStringB ((us, xs) \ M) =
    let
      val symEmpty = Sp.isEmpty us
      val varEmpty = Sp.isEmpty xs
      val us' = Sp.pretty ShowSym.toString "," us
      val xs' = Sp.pretty ShowVar.toString "," xs
    in
      (if symEmpty then "" else "{" ^ us' ^ "}")
        ^ (if varEmpty then "" else "[" ^ xs' ^ "]")
        ^ (if symEmpty andalso varEmpty then "" else ".")
        ^ toString M
    end

  val toStringAbs = toStringB o outb

end

functor PlainShowAbt (Abt : ABT) =
  ShowAbt
    (structure Abt = Abt
     and ShowVar = Abt.Var
     and ShowSym = Abt.Sym)

functor DebugShowAbt (Abt : ABT) =
  ShowAbt
    (structure Abt = Abt
     and ShowVar = Abt.Var.DebugShow
     and ShowSym = Abt.Sym.DebugShow)
