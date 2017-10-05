functor ShowAbt
  (structure Abt : ABT
   structure ShowVar : SHOW where type t = Abt.variable) :>
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
       | theta $ [] => O.toString theta
       | theta $ es =>
          O.toString theta
            ^ "(" ^ ListSpine.pretty toStringB "; " es ^ ")"
       | mv $# ms =>
           let
             val ms' = ListSpine.pretty toString "," ms
           in
             "#" ^ Abt.Metavar.toString mv
                 ^ (if ListSpine.isEmpty ms then "" else "[" ^ ms' ^ "]")
           end

  and toStringB (xs \ M) =
    let
      val varEmpty = ListSpine.isEmpty xs
      val xs' = ListSpine.pretty ShowVar.toString "," xs
    in
      (if varEmpty then "" else "[" ^ xs' ^ "].")
        ^ toString M
    end

  val toStringAbs = toStringB o outb

end

functor PlainShowAbt (Abt : ABT) =
  ShowAbt
    (structure Abt = Abt
     and ShowVar = Abt.Var)

functor DebugShowAbt (Abt : ABT) =
  ShowAbt
    (structure Abt = Abt
     and ShowVar = Abt.Var.DebugShow)
