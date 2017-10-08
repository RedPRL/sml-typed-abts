structure AbtViews : ABT_VIEWS =
struct
  datatype ('v, 'a) bindf =
     \ of ('v list) * 'a

  datatype ('var, 'mvar, 'op, 'a) termf =
      ` of 'var
    | $ of 'op * ('var, 'a) bindf list
    | $# of 'mvar * 'a list

  datatype ('var, 'op, 'a) appf =
     `$ of 'op * ('var, 'a) bindf list

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
