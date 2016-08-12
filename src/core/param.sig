signature ABT_PARAM =
sig
  include MONAD

  val extract : 'i t -> 'i option
  val eq : ('i * 'i -> bool) -> 'i t * 'i t -> bool
  val toString : ('i -> string) -> 'i t -> string
end
