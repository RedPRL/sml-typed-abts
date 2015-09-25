signature LIST_PRETTY =
sig
  val pretty : ('a -> string) -> string * 'a list -> string
end

