signature PARSE_OPERATOR =
sig
  structure Operator : OPERATOR

  val parse : string Operator.t CharParser.charParser
end
