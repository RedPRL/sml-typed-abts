signature EQ =
sig
  type t
  val eq : t * t -> bool
end

signature EQ1 =
sig
  type 'a t
  val eq : ('a * 'a -> bool) -> 'a t * 'a t -> bool
end

