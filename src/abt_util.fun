functor AbtUtil (Abt : ABT) : ABT_UTIL =
struct
  open Abt

  datatype star = STAR of star view | EMB of abt

  infixr 5 \
  infix 5 $

  structure Arity = Operator.Arity
  structure Spine = Arity.Valence.Spine

  fun checkStar (STAR (`x) , valence) = check (`x, valence)
    | checkStar (STAR (xs \ e), valence as (sorts, tau)) =
      let
        val e = checkStar (e, (Spine.empty, tau))
      in
        check (xs \ e, valence)
      end
    | checkStar (STAR (theta $ es), valence) =
      let
        val (valences, _) = Operator.arity theta
        val es = Spine.Pair.mapEq checkStar (es, valences)
      in
        check (theta $ es, valence)
      end
    | checkStar (EMB e, valence) =
      let
        val (valence', e') = infer e
        val true = Arity.Valence.eq (valence, valence')
      in
        e
      end
end

