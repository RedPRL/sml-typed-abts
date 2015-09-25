signature MONAD =
sig
  type 'a t
  val pure : 'a -> 'a t
  val bind : ('a -> 'b t) -> 'a t -> 'b t
end

