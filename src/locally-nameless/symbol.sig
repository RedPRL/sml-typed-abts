signature ABT_SYMBOL =
sig
  type t

  (* named gives back a [t] so that pretty-printing
   * the resulting [t] gives back the supplied name.
   *
   * There is no guarantee of freshness here.
   *)
  val named : string -> t

  val toString : t -> string
  val eq : t * t -> bool

  val compare : t * t -> order

  structure Ord : ORDERED where type t = t
  structure Ctx : DICT where type key = t
  type 'a ctx = 'a Ctx.dict

  val fresh : 'a Ctx.dict -> string -> t

  (* DebugShow will pretty print more than a symbol's name so
   * that one can distinguish between identically named symbols.
   *)
  structure DebugShow : SHOW where type t = t
end

signature ABT_IMPERATIVE_SYMBOL =
sig
  include ABT_SYMBOL

  val new : unit -> t
end
