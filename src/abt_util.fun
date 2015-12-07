functor AbtUtil (Abt : ABT) : ABT_UTIL =
struct
  open Abt

  datatype star = STAR of star view | EMB of abt

  infixr 5 \
  infix 5 $ $#

  structure Arity = Operator.Arity
  structure Valence = Arity.Valence
  structure Spine = Valence.Spine

  fun checkStar Theta M tau =
    case M of
         STAR (`x) => check Theta (`x, tau)
       | STAR (theta $ Es) =>
           let
             val (valences, _) = Operator.arity theta
             val Es' =
               Spine.Pair.mapEq
                 (fn (E, valence as (_, sigma)) =>
                     BFunctor.map (fn M => checkStar Theta M sigma) E)
                 (Es, valences)
           in
             check Theta (theta $ Es', tau)
           end
       | STAR (mv $# (us, Ms)) =>
           let
             val ((_, vsorts), tau) = Abt.Metacontext.lookup Theta mv
             val Ms' = Spine.Pair.mapEq (fn (M, sigma) => checkStar Theta M sigma) (Ms, vsorts)
           in
             check Theta (mv $# (us, Ms'), tau)
           end
       | EMB M =>
           let
             val (M', _) = infer M
           in
             check Theta (M', tau)
           end
end

