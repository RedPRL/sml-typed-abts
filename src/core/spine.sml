structure ListSpine :> SPINE  where type 'a t = 'a list =
struct
  type 'a t = 'a list
  open List

  fun empty () = []

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
    open List
  end

  structure Functor = Util
  structure Foldable = Util
end

structure VectorSpine :> SPINE where type 'a t = 'a Vector.vector =
struct
  open Vector

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
    open Vector
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
