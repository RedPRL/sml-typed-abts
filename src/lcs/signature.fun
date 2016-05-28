functor LcsSignature (structure L : LCS_LANGUAGE and Abt : ABT) : LCS_SIGNATURE =
struct
  open Abt
  type term = abt
  type sort = L.V.Arity.sort
  type valence = L.V.Arity.valence

  structure Dict = Symbol.Ctx

  type arguments = (metavariable * valence) list
  type symbols = (symbol * sort) list

  type def =
    {parameters : symbols,
     arguments : arguments,
     sort : sort,
     definiens : term}

  type t = def Dict.dict

  fun define sign opid def =
    Dict.insert sign opid def

  fun lookup sign opid =
    Dict.lookup sign opid
end
