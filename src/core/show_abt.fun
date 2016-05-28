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

  structure Sp = Abt.Operator.Ar.Vl.Sp

  fun toString M =
    case #1 (infer M) of
         `x => ShowVar.toString x
       | theta $ es =>
           if Sp.isEmpty es then
             Operator.toString ShowSym.toString theta
           else
             Operator.toString ShowSym.toString theta
                ^ "(" ^ Sp.pretty toStringB "; " es ^ ")"
       | mv $# (us, ms) =>
           let
             val us' = Sp.pretty (ShowSym.toString o #1) "," us
             val ms' = Sp.pretty toString "," ms
           in
             "#" ^ Abt.Metavariable.toString mv
                 ^ (if Sp.isEmpty us then "" else "{" ^ us' ^ "}")
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
     and ShowVar = Abt.Variable
     and ShowSym = Abt.Symbol)

functor DebugShowAbt (Abt : ABT) =
  ShowAbt
    (structure Abt = Abt
     and ShowVar = Abt.Variable.DebugShow
     and ShowSym = Abt.Symbol.DebugShow)
