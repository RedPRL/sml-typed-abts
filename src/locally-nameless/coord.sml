structure Coord :> COORD =
struct
  type t = int * int
  val origin = (0,0)
  fun shiftRight (i, j) = (i, j + 1)
  fun shiftDown (i, j) = (i + 1, j)

  structure Eq =
  struct
    type t = t
    fun eq (x : t, y : t) = x = y
  end
end

