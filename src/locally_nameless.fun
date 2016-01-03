functor LocallyNameless (Coord : COORD) : LOCALLY_NAMELESS =
struct
  structure Coord = Coord

  datatype 'a t =
      FREE of 'a
    | BOUND of Coord.t

  structure Eq : EQ1 =
  struct
    type 'a t = 'a t
    fun eq f (FREE v, FREE v') = f (v, v')
      | eq f (BOUND i, BOUND j) = Coord.Eq.eq (i, j)
      | eq _ _ = false
  end

  structure Functor : FUNCTOR =
  struct
    type 'a t = 'a t
    fun map f (FREE v) = FREE (f v)
      | map f (BOUND i) = BOUND i
  end

  structure Monad : MONAD =
  struct
    type 'a t = 'a t
    fun pure v = FREE v
    fun bind f (FREE v) = f v
      | bind f (BOUND i) = BOUND i
  end

  exception UnexpectedBoundName of Coord.t

  fun getFree (FREE v) = v
    | getFree (BOUND i) = raise UnexpectedBoundName i

end
