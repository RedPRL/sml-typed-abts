functor AbtUtil (Abt : ABT) : ABT_UTIL =
struct
  open Abt

  datatype star = STAR of star view | EMB of abt

  infixr 5 \
  infix 5 $

  structure Arity = Operator.Arity
  structure Valence = Arity.Valence
  structure Spine = Valence.Spine

  fun subst (rho as (e, x)) e' =
    case infer e' of
         (_, ` y) => if Variable.Eq.eq (x, y) then e else e'
       | (valence, xs \ e'') =>
           if Spine.exists (fn y => Variable.Eq.eq (x, y)) xs then
             e'
           else
             check (xs \ subst rho e'', valence)
       | (valence, theta $ es) =>
           check (theta $ Spine.Functor.map (subst rho) es, valence)

  fun checkStar (e, valence as (sorts, tau)) =
    case e of
         STAR (`x) => check (`x, valence)
       | STAR (xs \ e) =>
           let
             val e = checkStar (e, (Spine.empty (), tau))
           in
             check (xs \ e, valence)
           end
       | STAR (theta $ es) =>
           let
             val (_, (valences, _)) = Operator.proj theta
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

