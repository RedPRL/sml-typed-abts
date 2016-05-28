functor LcsSignature (structure L : LCS_LANGUAGE and Abt : ABT) : LCS_SIGNATURE =
struct
  open Abt
  type term = abt
  type sort = L.V.Ar.sort
  type valence = L.V.Ar.valence

  structure Dict = Symbol.Ctx

  type arguments = (metavariable * valence) list
  type symbols = (symbol * sort) list

  type def =
    {parameters : symbols,
     arguments : arguments,
     sort : sort,
     definiens : term}

  type t = def Dict.dict


  val empty = Dict.empty

  fun define sign opid def =
    Dict.insert sign opid def

  fun lookup sign opid =
    Dict.lookup sign opid
end
