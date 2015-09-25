functor FunctorOfMonad (M : MONAD) :> FUNCTOR where type 'a t = 'a M.t =
struct
  open M
  fun map f =
    bind (pure o f)
end
