functor AbtSyntaxView (Abt : ABT) : ABT_SYNTAX_VIEW =
struct
  open Abt
  type 'a operator = 'a Abt.O.t
  type term = abt

  structure Show = PlainShowAbt (Abt)
  structure DebugShow = DebugShowAbt (Abt)

  val toString = Show.toString
  val debugToString = DebugShow.toString
end

functor AstSyntaxView (Ast : AST where type 'a spine = 'a list) : ABT_SYNTAX_VIEW =
struct
  type symbol = Ast.symbol
  type variable = Ast.variable
  type metavariable = Ast.metavariable
  type sort = unit
  type 'a operator = 'a Ast.operator
  type 'a spine = 'a Ast.spine

  type term = Ast.ast

  datatype 'a bview =
     \ of (symbol spine * variable spine) * 'a

  datatype 'a view =
     ` of variable
   | $ of symbol operator * 'a bview spine
   | $# of metavariable * ((symbol * sort) spine * 'a spine)

  fun check (m, _) =
    case m of
       `x => Ast.` x
     | $ (th, es) => Ast.$ (th, List.map (fn \ ((us,xs), m) => Ast.\ ((us, xs), m)) es)
     | $# (x, (us, ms)) => Ast.$# (x, (List.map #1 us, ms))

  fun $$ (th, es) =
    check ($ (th, es), ())

  val out =
    fn Ast.`x => `x
     | Ast.$ (th, es) => $ (th, List.map (fn Ast.\ ((us, xs), m) => \ ((us, xs), m)) es)
     | Ast.$# (x, (us, ms)) => $# (x, (List.map (fn u => (u, ())) us, ms))

  fun infer m =
    (out m, ())

  val toString = Ast.toString
  val debugToString = Ast.toString
end
