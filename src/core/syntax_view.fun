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

functor AstSyntaxView
  (structure Ast : AST where type 'a spine = 'a list
   type sort) : ABT_SYNTAX_VIEW_INTO =
struct
  type symbol = Ast.symbol
  type variable = Ast.variable
  type metavariable = Ast.metavariable
  type sort = sort
  type 'a operator = 'a Ast.operator
  type 'a spine = 'a Ast.spine
  type 'a param = 'a Ast.P.t

  type term = Ast.ast

  datatype 'a bview =
     \ of (symbol spine * variable spine) * 'a

  datatype 'a view =
     ` of variable
   | $ of symbol param operator * 'a bview spine
   | $# of metavariable * ((symbol param * sort) spine * 'a spine)

  fun check (m, _) =
    case m of
       `x => Ast.` x
     | $ (th, es) => Ast.$ (th, List.map (fn \ ((us,xs), m) => Ast.\ ((us, xs), m)) es)
     | $# (x, (ps, ms)) => Ast.$# (x, (List.map #1 ps, ms))

  fun $$ (th, es) =
    check ($ (th, es), ())

  val toString = Ast.toString
  val debugToString = Ast.toString
end
