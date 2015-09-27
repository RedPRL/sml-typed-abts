functor AbtUtil (Abt : ABT) : ABT_UTIL =
struct
  open Abt

  datatype star = STAR of star view | EMB of abt

  infixr 5 \
  infix 5 $

  fun checkStar (STAR (`x) , valence) = check (`x, valence)
    | checkStar (STAR (xs \ ast), valence as (sorts, tau)) =
      let
        val e = checkStar (ast, ([], tau))
      in
        check (xs \ e, valence)
      end
    | checkStar (STAR (theta $ (asts : star spine)), valence) =
      let
        val (valences, _) = Operator.arity theta
        val es = Operator.Arity.Spine.Pair.mapEq checkStar (asts, valences)
      in
        check (theta $ es, valence)
      end
    | checkStar (EMB e, valence) =
      let
        val (valence', e') = infer e
        val true = Operator.Arity.Valence.eq (valence, valence')
      in
        e
      end
end

