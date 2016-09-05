functor AbtViews (Sp : SPINE) : ABT_VIEWS =
struct
  type 'a spine = 'a Sp.t

  datatype ('s, 'v, 'a) bindf =
     \ of ('s spine * 'v spine) * 'a

  datatype ('param, 'psort, 'sym, 'var, 'mvar, 'op, 'a) termf =
      ` of 'var
    | $ of 'op * ('sym, 'var, 'a) bindf spine
    | $# of 'mvar * (('param * 'psort) spine * 'a spine)

  datatype ('sym, 'var, 'op, 'a) appf =
     `$ of 'op * ('sym, 'var, 'a) bindf spine

  infix \ $ $# `$

  fun mapBind f ((us, xs) \ m) =
    (us, xs) \ f m

  fun map f =
    fn `x => `x
     | theta $ es =>
         theta $ Sp.map (mapBind f) es
     | mv $# (us, ms) =>
         mv $# (us, Sp.map f ms)

  fun mapApp f (theta `$ es) =
    theta `$ Sp.map (mapBind f) es

end
