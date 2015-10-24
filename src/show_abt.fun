functor ShowAbt
  (structure Abt : ABT
   structure ShowVar : SHOW where type t = Abt.variable
   structure ShowSym : SHOW where type t = Abt.symbol) :> SHOW where type t = Abt.abt =
struct
  open Abt infix $ infixr \
  type t = abt

  structure Spine = Abt.Operator.Arity.Valence.Spine

  structure OShow = Operator.Show (Abt.Symbol.Show)

  fun toString e =
    case #2 (infer e) of
         `x => ShowVar.toString x
       | (us, xs) \ e =>
           let
             val us' = Spine.pretty ShowSym.toString "," us
             val xs' = Spine.pretty ShowVar.toString "," xs
           in
             "{" ^ us' ^ "}[" ^ xs' ^ "]." ^ toString e
           end
       | theta $ es =>
           if Spine.isEmpty es then
             OShow.toString theta
           else
             OShow.toString theta
                ^ "(" ^ Spine.pretty toString "; " es ^ ")"
end

functor PlainShowAbt (Abt : ABT) =
  ShowAbt (structure Abt = Abt and ShowVar = Abt.Variable.Show and ShowSym = Abt.Symbol.Show)

functor DebugShowAbt (Abt : ABT) =
  ShowAbt (structure Abt = Abt and ShowVar = Abt.Variable.DebugShow and ShowSym = Abt.Symbol.DebugShow)


