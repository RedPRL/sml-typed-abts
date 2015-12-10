signature PRESYMBOL =
sig
  type t
  val named : string -> t

  structure Show : SHOW where type t = t
  structure Eq : EQ where type t = t

  val compare : t * t -> order
end

signature SYMBOL =
sig
  include PRESYMBOL
  val new : unit -> t
  val clone : t -> t

  structure DebugShow : SHOW where type t = t
end

