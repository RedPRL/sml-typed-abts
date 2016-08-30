functor AbtParameterUtil (P : ABT_PARAMETER) : ABT_PARAMETER_UTIL =
struct
  structure P = P

  type 'a t = 'a P.term
  val pure = P.VAR

  fun bind f =
    fn P.VAR x => f x
     | P.APP t => P.APP (P.map (bind f) t)

  fun eq f =
    fn (P.VAR x, P.VAR y) => f (x, y)
     | (P.APP t1, P.APP t2) => P.eq (eq f) (t1, t2)
     | _ => false

  fun toString f =
    fn P.VAR x => f x
     | P.APP t => P.toString (toString f) t
end

structure AbtEmptyParameter : ABT_PARAMETER =
struct
  datatype 'a t = NOPE of 'a t
  datatype 'a term =
     VAR of 'a
   | APP of 'a term t

  fun map f (NOPE t) = raise Match
  fun eq _ _ = true
  fun toString _ _ = raise Match

  fun join z m (NOPE t) = raise Match
end
