structure AbtViews : ABT_VIEWS =
struct
  type 'a spine = 'a list

  datatype ('v, 'a) bindf =
     \ of ('v spine) * 'a

  datatype ('var, 'mvar, 'op, 'a) termf =
      ` of 'var
    | $ of 'op * ('var, 'a) bindf spine
    | $# of 'mvar * 'a spine

  datatype ('var, 'op, 'a) appf =
     `$ of 'op * ('var, 'a) bindf spine

  infix \ $ $# `$

  fun mapBind f (xs \ m) =
    xs \ f m

  fun map f =
    fn `x => `x
     | theta $ es =>
         theta $ List.map (mapBind f) es
     | mv $# ms =>
         mv $# List.map f ms

  fun mapApp f (theta `$ es) =
    theta `$ List.map (mapBind f) es

end
