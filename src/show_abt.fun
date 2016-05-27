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

  structure Spine = Abt.Operator.Arity.Valence.Spine

  fun toString M =
    case #1 (infer M) of
         `x => ShowVar.toString x
       | theta $ es =>
           if Spine.isEmpty es then
             Operator.toString ShowSym.toString theta
           else
             Operator.toString ShowSym.toString theta
                ^ "(" ^ Spine.pretty toStringB "; " es ^ ")"
       | mv $# (us, ms) =>
           let
             val us' = Spine.pretty (ShowSym.toString o #1) "," us
             val ms' = Spine.pretty toString "," ms
           in
             "#" ^ Abt.Metavariable.toString mv
                 ^ (if Spine.isEmpty us then "" else "{" ^ us' ^ "}")
                 ^ (if Spine.isEmpty ms then "" else "[" ^ ms' ^ "]")
           end

  and toStringB ((us, xs) \ M) =
    let
      val symEmpty = Spine.isEmpty us
      val varEmpty = Spine.isEmpty xs
      val us' = Spine.pretty ShowSym.toString "," us
      val xs' = Spine.pretty ShowVar.toString "," xs
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
