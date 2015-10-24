functor AbtUtil (Abt : ABT) : ABT_UTIL =
struct
  open Abt

  datatype star = STAR of star view | EMB of abt

  infixr 5 \
  infix 5 $ $#

  structure Arity = Operator.Arity
  structure Valence = Arity.Valence
  structure Spine = Valence.Spine

  fun checkStar Omega (e, valence as ((symbols, variables), tau)) =
    case e of
         STAR (`x) => check Omega (`x, valence)
       | STAR ((us, xs) \ e) =>
           let
             val e = checkStar Omega (e, ((Spine.empty (), Spine.empty ()), tau))
           in
             check Omega ((us, xs) \ e, valence)
           end
       | STAR (theta $ es) =>
           let
             val (valences, _) = Operator.arity theta
             val es = Spine.Pair.mapEq (checkStar Omega) (es, valences)
           in
             check Omega (theta $ es, valence)
           end
       | STAR (mv $# (us, es)) =>
           let
             val ((symbolSorts, variableSorts), tau) = Abt.Metacontext.lookup Omega mv
             val valences = Spine.Functor.map (fn sigma => ((Spine.empty (), Spine.empty ()), sigma)) symbolSorts
             val es = Spine.Pair.mapEq (checkStar Omega) (es, valences)
           in
             check Omega (mv $# (us, es), valence)
           end
       | EMB e =>
           let
             val (valence', e') = infer Omega e
             val true = Arity.Valence.Eq.eq (valence, valence')
           in
             if Arity.Valence.Eq.eq (valence, valence') then
               e
             else
               raise Fail ("Expected valence " ^ Valence.Show.toString valence ^ " but got " ^ Valence.Show.toString valence')
           end
end

