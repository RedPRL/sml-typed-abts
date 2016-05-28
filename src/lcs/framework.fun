functor LcsFramework (L : LCS_LANGUAGE) : LCS_FRAMEWORK =
struct
  structure Operator = LcsOperator (L)
  structure Sort = Operator.Sort
  structure Abt = SimpleAbt (Operator)
  structure Sig = LcsSignature (structure L = L and Abt = Abt)
  structure Dynamics = LcsDynamics (structure L = L and O = Operator and Abt = Abt and Sig = Sig)
end
