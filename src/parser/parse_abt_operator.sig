signature PARSE_ABT_OPERATOR =
sig
  structure Operator : ABT_OPERATOR

  val parseParam : string Operator.P.t CharParser.charParser
  val parse : string Operator.P.t Operator.t CharParser.charParser
end
