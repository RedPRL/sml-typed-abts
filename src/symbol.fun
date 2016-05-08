functor Symbol () :> IMPERATIVE_SYMBOL =
struct
  type t = int * string
  val counter = ref 0

  fun named a =
    let
      val i = !counter
      val _ = counter := i + 1
    in
      (i, a)
    end

  fun new () =
    named "@"

  fun fresh _ =
    named

  fun compare ((i, _), (j, _)) =
    Int.compare (i, j)

  fun eq ((i : int, _), (j, _)) = i = j

  fun clone (_, a) =
    named a

  fun toString (_, a) = a

  structure DebugShow =
  struct
    type t = t
    fun toString (i, a) =
      a ^ "@" ^ Int.toString i
  end
end

structure StringPresymbol : PRESYMBOL =
struct
  type t = string
  fun named x = x

  fun toString x = x
  fun eq (x : t, y) = x = y

  val compare = String.compare
end
