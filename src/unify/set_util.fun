functor SetUtil (S : SET) :
sig
  include SET

  exception Duplicate
  val insertDistinct : set -> elem -> set

  val fromList : elem list -> set
  val fromListDistinct : elem list -> set
end =
struct
  open S
  exception Duplicate

  fun insertDistinct s e =
    if member s e then
      raise Duplicate
    else
      insert s e

  val fromList = List.foldl (fn (e, s) => insert s e) empty
  val fromListDistinct = List.foldl (fn (e, s) => insertDistinct s e) empty
end
