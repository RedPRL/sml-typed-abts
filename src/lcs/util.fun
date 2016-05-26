functor LcsUtil
  (structure Operator : LCS_OPERATOR
   structure Abt : ABT
     where type 'a Operator.t = 'a Operator.t
     where type 'a Operator.Arity.Valence.Spine.t = 'a Operator.Arity.Valence.Spine.t) : LCS_UTIL =
struct
  structure Abt = Abt

  exception hole
  fun ?e = raise e

  structure O = Operator

  local
    open Abt LcsCanonicity
    infix $ \ $#
  in
    fun neutral m =
      case out m of
         `_ => true
       | theta $ es =>
           (case O.canonicity theta of
              CAN => false
            | NCAN => List.all neutralB (O.criticalArguments theta es))
       | _ $# _ => true
    and neutralB (_ \ m) = neutral m
  end
end
