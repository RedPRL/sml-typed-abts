functor AbtSimpleOperator (O : ABT_SIMPLE_OPERATOR) : ABT_OPERATOR =
struct
  structure Arity = O.Arity

  type 'i t = O.t
  val arity = O.arity
  fun support _ = []
  fun eq _ = O.eq
  fun toString _ = O.toString
  fun map f x = x
end
