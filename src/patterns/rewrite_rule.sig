signature REWRITE_RULE =
sig
  type term
  type pattern

  type rule
  datatype view = ~> of pattern * term

  exception InvalidRule
  val into : view -> rule
  val out : rule -> view

  exception RuleInapplicable
  val compile : rule -> term -> term
end
