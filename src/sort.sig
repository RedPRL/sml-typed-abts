signature SORT =
sig
  type t
  structure Eq : EQ where type t = t
  structure Show : SHOW where type t = t
end

