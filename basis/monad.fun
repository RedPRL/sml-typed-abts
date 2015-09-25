structure ListMonad :> MONAD where type 'a t = 'a list =
struct
  type 'a t = 'a list
  fun pure x = [x]
  fun bind f =
    let
      fun go [] = []
        | go (x :: xs) = f x @ go xs
    in
      go
    end
end

structure ListFunctor = FunctorOfMonad (ListMonad)
