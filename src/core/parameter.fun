functor AbtParameterTerm (Sig : ABT_PARAMETER) : ABT_PARAMETER_TERM =
struct
  structure Sig = Sig

  datatype 'a term =
     VAR of 'a
   | APP of 'a term Sig.t

  structure Monad =
  struct
    type 'a t = 'a term
    val ret = VAR

    fun bind f =
      fn VAR x => f x
       | APP t => APP (Sig.map (bind f) t)
  end

  structure Functor = MonadApplicative (Monad)
  open Monad Functor

  fun eq f =
    fn (VAR x, VAR y) => f (x, y)
     | (APP t1, APP t2) => Sig.eq (eq f) (t1, t2)
     | _ => false

  fun toString f =
    fn VAR x => f x
     | APP t => Sig.toString (toString f) t

  fun collectSubterms t =
    Sig.join [] op@ (Sig.map ListMonad.ret t)

  exception SortError

  fun check tau =
    fn VAR x => [(x, tau)]
     | APP t =>
         let
           val (sigmas, tau') = Sig.arity t
           val annotatedSubterms = ListPair.zip (collectSubterms t, collectSubterms sigmas)
         in
           if Sig.Sort.eq (tau, tau') then
             ListMonad.bind
               (fn (m, sigma) => check sigma m)
               annotatedSubterms
           else
             raise SortError
         end

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
