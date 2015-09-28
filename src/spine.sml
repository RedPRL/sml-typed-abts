functor ListSpine (L : LIST where type 'a list = 'a list) :> SPINE  where type 'a t = 'a list=
struct
  open L

  type 'a t = 'a list

  fun empty () = []

  val all = L.all
  val exists = L.exists

  fun isEmpty [] = true
    | isEmpty _ = false

  fun pretty f sep =
    let
      fun go [] = ""
        | go (x :: []) = f x
        | go (x :: xs) = f x ^ sep ^ go xs
    in
      go
    end

  structure Pair = ListPair
  structure Util =
  struct
    type 'a t = 'a t
    open L
  end

  structure Functor = Util
  structure Foldable = Util
end

structure ListSpine = ListSpine (List)

functor VectorSpine (V : VECTOR) :> SPINE where type 'a t = 'a V.vector =
struct
  open V

  type 'a t = 'a vector
  fun empty () = fromList []
  fun isEmpty xs = length xs = 0

  fun pretty f sep v =
    let
      val n = length v
      fun go (i, s1, s2) =
        if i = n - 1 then
          s1
        else
          s1 ^ sep ^ s2
    in
      foldri go "" (map f v)
    end

  structure Util =
  struct
    type 'a t = 'a t
    open V
  end

  structure Functor = Util
  structure Foldable = Util

  structure Pair =
  struct
    exception UnequalLengths

    fun mapEq f (v1, v2) =
      let
        val len = length v1
        val () = if length v2 <> len then raise UnequalLengths else ()
      in
        tabulate (len, fn n => f (sub (v1, n), sub (v2, n)))
      end

    fun zipEq vv = mapEq (fn x => x) vv

    fun allEq p (v1, v2) =
      all p (zipEq (v1, v2))
  end
end

structure VectorSpine = VectorSpine (Vector)
