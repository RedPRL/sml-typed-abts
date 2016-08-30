signature PARSE_ABT_OPERATOR =
sig
  structure Operator : ABT_OPERATOR

  val parse : string Operator.t CharParser.charParser
  val parseParam : string Operator.P.term CharParser.charParser
end
