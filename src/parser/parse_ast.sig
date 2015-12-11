signature PARSE_AST =
sig
  structure ParseOperator : PARSE_OPERATOR
  structure Ast : AST

  sharing type Ast.operator = ParseOperator.Operator.t

  val parse : Ast.ast CharParser.charParser
end
