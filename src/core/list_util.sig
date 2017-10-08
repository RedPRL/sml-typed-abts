signature LIST_UTIL = 
sig
  val isEmpty : 'a list -> bool
  val joinWith : ('a -> string) -> string -> 'a list -> string
end