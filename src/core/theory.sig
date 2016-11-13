signature LAWVERE_THEORY =
sig
  type sort
  type var
  type ctx

  type term

  val empty : term
  val fork : var * term -> var * term -> term
  val proj : ctx -> term

  val ctx : term -> ctx

  val subst : term -> term -> term

  val lookup : var -> term -> term
end
