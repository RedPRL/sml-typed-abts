functor UnorderedContext
  (structure Key : PRESYMBOL
   structure Elem : EQ
  ) :> UNORDERED_CONTEXT
         where type key = Key.t
           and type elem = Elem.t =
struct
  type key = Key.t
  type elem = Elem.t

  structure Ctx = SplayDict (structure Key = Key)
  type t = elem Ctx.dict

  exception KeyNotFound
  exception MergeFailure

  val empty = Ctx.empty
  val isEmpty = Ctx.isEmpty
  val toList = Ctx.toList

  fun merge (v, v') =
    if Elem.eq (v, v') then
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
      handle _ => raise KeyNotFound

  val find = Ctx.find

end
