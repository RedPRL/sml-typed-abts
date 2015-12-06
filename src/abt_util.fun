functor AbtUtil (Abt : ABT) : ABT_UTIL =
struct
  open Abt

  datatype star = STAR of star view | EMB of abt

  infixr 5 \
  infix 5 $

  structure Arity = Operator.Arity
  structure Valence = Arity.Valence
  structure Spine = Valence.Spine

  fun checkStar (e, valence as ((symbols, variables), tau)) =
    case e of
         STAR (`x) => check (`x, valence)
       | STAR ((us, xs) \ e) =>
           let
             val e = checkStar (e, ((Spine.empty (), Spine.empty ()), tau))
           in
             check ((us, xs) \ e, valence)
           end
       | STAR (theta $ es) =>
           let
             val (valences, _) = Operator.arity theta
             val es = Spine.Pair.mapEq checkStar (es, valences)
           in
             check (theta $ es, valence)
           end
       | EMB e =>
           let
             val (valence', e') = infer e
             val true = Arity.Valence.Eq.eq (valence, valence')
           in
             if Arity.Valence.Eq.eq (valence, valence') then
               e
             else
               raise Fail ("Expected valence " ^ Valence.Show.toString valence ^ " but got " ^ Valence.Show.toString valence')
           end
end

