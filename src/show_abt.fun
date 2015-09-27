functor ShowAbt
  (structure Abt : ABT
   structure ShowVar : SHOW
     where type t = Abt.variable) :> SHOW where type t = Abt.abt =
struct
  open Abt infix $ infixr \
  type t = abt

  fun toString e =
    case #2 (infer e) of
         `x => ShowVar.toString x
       | xs \ e =>
           ListPretty.pretty ShowVar.toString (",", xs)
              ^ "." ^ toString e
       | theta $ es =>
           Operator.toString theta
              ^ "(" ^ Abt.Operator.Arity.Spine.pretty toString "; " es ^ ")"
end

functor PlainShowAbt (Abt : ABT) =
  ShowAbt (structure Abt = Abt and ShowVar = Abt.Variable.Show)

functor DebugShowAbt (Abt : ABT) =
  ShowAbt (structure Abt = Abt and ShowVar = Abt.Variable.DebugShow)


