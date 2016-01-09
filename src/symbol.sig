(* A PRESYMBOL is just something that captures the notion of a named
 * object. It should not be expected that [compare] is a very meaningful
 * ordering but without such a thing it becomes impossible to efficiently
 * maintain maps of PRESYMBOL like things
 *)
signature PRESYMBOL =
sig
  type t

  (* named gives back a [t] so that pretty-printing
   * the resulting [t] gives back the supplied name.
   *
   * There is no guarantee of freshness here.
   *)
  val named : string -> t

  structure Show : SHOW where type t = t
  structure Eq : EQ where type t = t

  val compare : t * t -> order
end

(* A SYMBOL adds the ability to generate fresh symbols. Specifically,
 * [new] and [clone] should return symbols that are different (according
 * to the equality function) even though they may print identically
 *
 * Symbols are slightly more exotic and often confused with variables.
 * They are objects which
 *   1. Parameterize *operators* instead of appearing raw
 *   2. ARE NOT DETERMINED BY SUBSTITUTION
 *   3. Vary by apartness preserving renamings
 *)
signature SYMBOL =
sig
  include PRESYMBOL
  val new : unit -> t
  val clone : t -> t

  (* DebugShow will pretty print more than a symbols name so
   * that one can distinguish between identically named symbols.
   *)
  structure DebugShow : SHOW where type t = t
end
