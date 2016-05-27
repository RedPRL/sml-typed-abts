functor LcsFramework (L : LCS_LANGUAGE) : LCS_FRAMEWORK =
struct
  structure Operator = LcsOperator (L)
  structure Sort = Operator.Sort
  structure Abt = SimpleAbt (Operator)
  structure Dynamics = LcsDynamics (structure L = L and O = Operator and Abt = Abt)
end
