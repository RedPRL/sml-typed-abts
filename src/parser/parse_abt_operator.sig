signature PARSE_ABT_OPERATOR =
sig
  structure Operator : ABT_OPERATOR

  val parse : string Operator.t CharParser.charParser
end
