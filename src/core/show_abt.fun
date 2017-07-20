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

  fun toString M =
    case #1 (infer M) of
         `x => ShowVar.toString x
       | theta $ [] => O.toString ShowSym.toString theta
       | theta $ es =>
          O.toString ShowSym.toString theta
            ^ "(" ^ ListSpine.pretty toStringB "; " es ^ ")"
       | mv $# (ps, ms) =>
           let
             val ps' = ListSpine.pretty (Abt.O.P.toString Sym.toString o #1) "," ps
             val ms' = ListSpine.pretty toString "," ms
           in
             "#" ^ Abt.Metavar.toString mv
                 ^ (if ListSpine.isEmpty ps then "" else "{" ^ ps' ^ "}")
                 ^ (if ListSpine.isEmpty ms then "" else "[" ^ ms' ^ "]")
           end

  and toStringB ((us, xs) \ M) =
    let
      val symEmpty = ListSpine.isEmpty us
      val varEmpty = ListSpine.isEmpty xs
      val us' = ListSpine.pretty ShowSym.toString "," us
      val xs' = ListSpine.pretty ShowVar.toString "," xs
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
