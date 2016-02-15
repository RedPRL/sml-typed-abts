functor LocallyNameless (Coord : COORD) : LOCALLY_NAMELESS =
struct
  structure Coord = Coord

  datatype 'a t =
      FREE of 'a
    | BOUND of Coord.t

  fun eq f (FREE v, FREE v') = f (v, v')
    | eq f (BOUND i, BOUND j) = Coord.eq (i, j)
    | eq _ _ = false

  fun map f (FREE v) = FREE (f v)
    | map f (BOUND i) = BOUND i

  fun toString f (FREE v) = f v
    | toString f (BOUND i) = Coord.toString i

  fun pure v = FREE v
  fun bind f (FREE v) = f v
    | bind f (BOUND i) = BOUND i

  exception UnexpectedBoundName of Coord.t

  fun getFree (FREE v) = v
    | getFree (BOUND i) = raise UnexpectedBoundName i

end
