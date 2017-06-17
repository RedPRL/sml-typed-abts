functor AbtSymbol () :> ABT_IMPERATIVE_SYMBOL =
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

  fun clone (_, a) =
    named a

  fun toString (_, a) = a

  structure Ord =
  struct
    type t = t

    fun eq ((i : int, _), (j, _)) =
      i = j

    fun compare ((i, _), (j, _)) =
      Int.compare (i, j)
  end

  open Ord

  structure Ctx = SplayDict (structure Key = Ord)
  type 'a ctx = 'a Ctx.dict

  structure DebugShow =
  struct
    type t = t
    fun toString (i, a) =
      a ^ "@" ^ Int.toString i
  end
end

structure StringAbtSymbol : ABT_SYMBOL =
struct
  type t = string

  structure Ord = StringOrdered
  structure Ctx = SplayDict (structure Key = Ord)
  type 'a ctx = 'a Ctx.dict

  open Ord

  fun named x = x
  fun toString x = x

  fun fresh ctx x =
    if Ctx.member ctx x then
      fresh ctx (x ^ "'")
    else
      x

  structure DebugShow =
  struct
    type t = t
    fun toString x = x
  end
end
