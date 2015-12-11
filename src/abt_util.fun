functor AbtUtil (Abt : ABT) : ABT_UTIL =
struct
  open Abt

  datatype star = STAR of star view | EMB of abt

  infixr 5 \
  infix 5 $ $#

  structure Arity = Operator.Arity
  structure Valence = Arity.Valence
  structure Spine = Valence.Spine

  fun checkStar Th m tau =
    case m of
         STAR (`x) => check Th (`x, tau)
       | STAR (theta $ es) =>
           let
             val (vls, _) = Operator.arity theta
             val es' =
               Spine.Pair.mapEq
                 (fn (e, vl as (_, sigma)) =>
                     BFunctor.map (fn n => checkStar Th n sigma) e)
                 (es, vls)
           in
             check Th (theta $ es', tau)
           end
       | STAR (mv $# (us, ms)) =>
           let
             val ((_, vsorts), tau) = Abt.Metacontext.lookup Th mv
             val ms' = Spine.Pair.mapEq (fn (n, sigma) => checkStar Th n sigma) (ms, vsorts)
           in
             check Th (mv $# (us, ms'), tau)
           end
       | EMB M =>
           let
             val (M', _) = infer M
           in
             check Th (M', tau)
           end
end

