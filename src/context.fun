functor Metacontext
  (structure Metavariable : PRESYMBOL
   structure Valence : EQ
  ) :> METACONTEXT
         where type metavariable = Metavariable.t
           and type valence = Valence.t =
struct
  type metavariable = Metavariable.t
  type valence = Valence.t

  structure Ctx = SplayDict (structure Key = Metavariable)
  type t = valence Ctx.dict

  exception MetavariableNotFound
  exception MergeFailure

  val empty = Ctx.empty
  val isEmpty = Ctx.isEmpty
  val toList = Ctx.toList

  fun merge (v, v') =
    if Valence.eq (v, v') then
      v'
    else
      raise MergeFailure

  fun extend Th (m, v) =
    Ctx.insertMerge Th m v
      (fn v' => merge (v, v'))

  fun extendUnique Th (m, v) =
    Ctx.insertMerge Th m v
      (fn _ => raise MergeFailure)

  fun union (Th, Th') =
    Ctx.union Th Th'
      (fn (_, v, v') => merge (v, v'))

  fun concat (Th, Th') =
    Ctx.union Th Th'
      (fn _ => raise MergeFailure)

  fun lookup Th m =
    Ctx.lookup Th m
      handle _ => raise MetavariableNotFound

  val find = Ctx.find

end
