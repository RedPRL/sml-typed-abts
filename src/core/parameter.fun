functor AbtParameterTerm (Sig : ABT_PARAMETER) : ABT_PARAMETER_TERM =
struct
  structure Sig = Sig

  datatype 'a term =
     VAR of 'a
   | APP of 'a term Sig.t

  structure Monad =
  struct
    type 'a t = 'a term
    val pure = VAR

    fun bind f =
      fn VAR x => f x
       | APP t => APP (Sig.map (bind f) t)
  end

  structure Functor = FunctorOfMonad (Monad)
  open Monad Functor

  fun eq f =
    fn (VAR x, VAR y) => f (x, y)
     | (APP t1, APP t2) => Sig.eq (eq f) (t1, t2)
     | _ => false

  fun toString f =
    fn VAR x => f x
     | APP t => Sig.toString (toString f) t

  fun collectSubterms t =
    Sig.join [] op@ (Sig.map ListMonad.pure t)

  fun freeVars t =
    let
      val (sigmas, _) = Sig.arity t
      val annotatedSubterms = ListPair.zip (collectSubterms t, collectSubterms sigmas)
    in
      ListMonad.bind
        (fn (VAR x, sigma) => [(x,sigma)]
          | (APP t, _) => freeVars t)
        annotatedSubterms
    end
end

functor AbtEmptyParameter (S : ABT_SORT) : ABT_PARAMETER =
struct
  structure Sort = S
  datatype 'a t = NOPE of 'a t

  fun arity _ = raise Match
  fun map _ _ = raise Match
  fun eq _ _ = raise Match
  fun toString _ _ = raise Match

  fun join z m _ = raise Match
end
