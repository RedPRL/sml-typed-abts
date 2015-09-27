functor RoseTree (Forest : SPINE) : ROSE_TREE =
struct
  structure Forest = Forest
  datatype 'a t = NIL | @^ of 'a * 'a t forest
  withtype 'a forest = 'a Forest.t
end

functor RoseTreeSpine (R : ROSE_TREE) : SPINE where type 'a t = 'a R.t =
struct
  open R

  val empty = NIL
  fun isEmpty NIL = true
    | isEmpty _ = false

  infix @^

  fun pretty f sep =
    let
      fun go NIL = "[]"
        | go (a @^ ts) = f a ^ " ^ [" ^ Forest.pretty go sep ts ^ "]"
    in
      go
    end

  structure Functor : FUNCTOR =
  struct
    type 'a t = 'a t
    fun map f =
      let
        fun go NIL = NIL
          | go (a @^ ts) = f a @^ Forest.Functor.map go ts
      in
        go
      end
  end

  structure Foldable : FOLDABLE =
  struct
    type 'a t = 'a t
    fun foldr f =
      let
        fun go m NIL = m
          | go m (a @^ ts) =
            f (a, Forest.Foldable.foldr (fn (t, m') => go m' t) m ts)
      in
        go
      end
  end

  structure Pair =
  struct
    exception UnequalLengths

    fun wrapExn f x =
      f x handle ListSpine.Pair.UnequalLengths => raise UnequalLengths
               | E => raise E

    fun mapEq f =
      let
        fun go (NIL, NIL) = NIL
          | go (a @^ ts, b @^ ts') =
              f (a, b) @^ Forest.Pair.mapEq go (ts, ts')
          | go _ = raise UnequalLengths
      in
        wrapExn go
      end

    fun allEq p =
      let
        fun go (NIL, NIL) = true
          | go (a @^ ts, b @^ ts') =
              p (a, b) andalso Forest.Pair.allEq go (ts, ts')
          | go _ = raise UnequalLengths
      in
        wrapExn go
      end

    fun zipEq tt = mapEq (fn x => x) tt
  end

end

structure RoseTree = RoseTree (ListSpine)
