functor ShowAbt
  (structure Abt : ABT
   structure ShowMetavar : SHOW where type t = Abt.metavariable
   structure ShowVar : SHOW where type t = Abt.variable
   structure ShowSym : SHOW where type t = Abt.symbol) :> SHOW where type t = Abt.abt =
struct
  open Abt infix $ $# infixr \
  type t = abt

  structure Spine = Abt.Operator.Arity.Valence.Spine
  structure SShow = Abt.Symbol.Show

  fun toString M =
    case #1 (infer M) of
         `x => ShowVar.toString x
       | theta $ es =>
           if Spine.isEmpty es then
             Operator.toString SShow.toString theta
           else
             Operator.toString SShow.toString theta
                ^ "(" ^ Spine.pretty toStringB "; " es ^ ")"
       | mv $# (us, es) =>
           let
             val us' = Spine.pretty ShowSym.toString "," us
             val es' = Spine.pretty toString "," es
           in
             "#" ^ ShowMetavar.toString mv
                 ^ (if Spine.isEmpty us then "" else "{" ^ us' ^ "}")
                 ^ (if Spine.isEmpty es then "" else "[" ^ es' ^ "]")
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


end

functor PlainShowAbt (Abt : ABT) =
  ShowAbt
    (structure Abt = Abt
     and ShowMetavar = Abt.Metavariable.Show
     and ShowVar = Abt.Variable.Show
     and ShowSym = Abt.Symbol.Show)

functor DebugShowAbt (Abt : ABT) =
  ShowAbt
    (structure Abt = Abt
     and ShowMetavar = Abt.Metavariable.DebugShow
     and ShowVar = Abt.Variable.DebugShow
     and ShowSym = Abt.Symbol.DebugShow)


