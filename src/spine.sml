structure ListSpine : SPINE =
struct
  type 'a t = 'a list

  val empty = []

  fun pretty f sep xs = ListPretty.pretty f (sep, xs)

  structure Pair = ListPair
  structure Functor =
  struct
    type 'a t = 'a t
    val map = List.map
  end
end
