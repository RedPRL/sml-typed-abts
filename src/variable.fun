functor Variable () :> VARIABLE =
struct
  type variable = int * string
  type t = variable
  val counter = ref 0
  fun named a =
    let
      val i = !counter
      val _ = counter := i + 1
    in
      (i, a)
    end

  fun compare ((i, _), (j, _)) =
    Int.compare (i, j)

  fun eq ((i : int, _), (j, _)) =
    i = j

  fun clone (_, a) =
    named a

  structure Show =
  struct
    type t = variable
    fun toString (_, a) = a
  end

  structure DebugShow =
  struct
    type t = variable
    fun toString (i, a) =
      a ^ "@" ^ Int.toString i
  end
end

