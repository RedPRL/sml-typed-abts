
functor AbtEmptyOperator (Ar : ABT_ARITY) : ABT_OPERATOR =
struct
  structure Ar = Ar

  datatype t = WELP of t

  fun arity (WELP x) = arity x
  fun eq (WELP x, WELP y) = eq (x, y)
  fun toString (WELP x) = toString x
end
