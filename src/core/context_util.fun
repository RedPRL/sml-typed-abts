functor ContextUtil (structure Ctx : DICT and Elem : EQ) : CONTEXT_UTIL =
struct
  open Ctx

  type elem = Elem.t
  type t = elem Ctx.dict

  exception KeyNotFound
  exception MergeFailure

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
end
