signature SHOW =
sig
  type t
  val toString : t -> string
end

signature SHOW1 =
sig
  type 'a t
  val toString : ('a -> string) -> 'a t -> string
end
