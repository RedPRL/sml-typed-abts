(* Extensible signatures *)
signature LCS_SIGNATURE =
sig
  type t

  type valence
  type sort

  type metavariable
  type symbol
  type term

  type arguments = (metavariable * valence) list
  type symbols = (symbol * sort) list

  type def =
    {parameters : symbols,
     arguments : arguments,
     sort : sort,
     definiens : term}

  val define : t -> symbol -> def -> t
  val lookup : t -> symbol -> def
end
