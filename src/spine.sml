structure ListSpine : SPINE =
struct
  type 'a t = 'a list

  val empty = []
  val all = List.all

  fun isEmpty [] = true
    | isEmpty _ = false

  fun pretty f sep xs = ListPretty.pretty f (sep, xs)

  structure Pair = ListPair
  structure Functor =
  struct
    type 'a t = 'a t
    val map = List.map
  end

  structure Foldable =
  struct
    type 'a t = 'a list
    val foldr = List.foldr
  end
end
