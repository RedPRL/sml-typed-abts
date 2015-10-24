signature SYMBOL =
sig
  type t
  val named : string -> t

  structure Show : SHOW where type t = t
  structure DebugShow : SHOW where type t = t
  structure Eq : EQ where type t = t

  val compare : t * t -> order
  val clone : t -> t
end

