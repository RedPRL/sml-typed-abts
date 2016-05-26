signature LCS_OPERATOR =
sig
  include OPERATOR

  type world

  val canonicity
    : 'a t
    -> LcsCanonicity.canonicity

  val criticalArguments
    : 'a t
    -> 'b Arity.spine
    -> 'b list
end
