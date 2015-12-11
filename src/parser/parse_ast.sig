signature PARSE_AST =
sig
  structure Ast : AST
  structure ParseOperator : PARSE_OPERATOR
  sharing type Ast.operator = ParseOperator.Operator.t

  type metavariable_table = string -> Ast.metavariable
  val parse : metavariable_table -> Ast.ast CharParser.charParser
end
