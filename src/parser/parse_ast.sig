signature PARSE_AST =
sig
  structure Ast : AST
  structure ParseOperator : PARSE_ABT_OPERATOR
  sharing type Ast.operator = ParseOperator.Operator.t

  type metavariable_table = string -> Ast.metavariable

  (* a basic parser for abstract [ast] notation *)
  val parse
    : metavariable_table (* free metavariables *)
    -> Ast.ast CharParser.charParser (* [ast] parser *)

  (* extend an [ast] parser with custom notation *)
  val extend
    : metavariable_table (* free metavariables *)
    -> Ast.ast CharParser.charParser (* custom notation *)
    -> Ast.ast CharParser.charParser (* [ast] parser *)
end
