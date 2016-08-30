functor AbtParameterTerm (Sig : ABT_PARAMETER) : ABT_PARAMETER_TERM =
struct
  structure Sig = Sig

  datatype 'a term =
     VAR of 'a
   | APP of 'a term Sig.t

  type 'a t = 'a term
  val pure = VAR

  fun bind f =
    fn VAR x => f x
     | APP t => APP (Sig.map (bind f) t)

  fun eq f =
    fn (VAR x, VAR y) => f (x, y)
     | (APP t1, APP t2) => Sig.eq (eq f) (t1, t2)
     | _ => false

  fun toString f =
    fn VAR x => f x
     | APP t => Sig.toString (toString f) t

  fun collectSubterms t =
    Sig.join [] op@ (Sig.map ListMonad.pure t)
end

structure AbtEmptyParameter : ABT_PARAMETER =
struct
  datatype 'a t = NOPE of 'a t

  fun map f (NOPE t) = raise Match
  fun eq _ _ = true
  fun toString _ _ = raise Match

  fun join z m (NOPE t) = raise Match
end
