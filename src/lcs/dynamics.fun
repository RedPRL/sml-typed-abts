functor LcsDynamics
  (structure Lcs : LCS_DEFINITION
   structure Closure : LCS_CLOSURE where type 'a Abt.Operator.Arity.Valence.Spine.t = 'a list
   sharing type Closure.Abt.Operator.t = Lcs.O.operator) : LCS_DYNAMICS =
struct

  structure Lcs = Lcs and Closure = Closure

  open Closure Lcs
  open Abt
  infix 1 <:
  infix 2 $ $$ $# \

  fun @@ (f, x) = f x
  infix 0 @@

  fun quoteB ((us, vs) \ m) =
    P.\ ((us, vs), m)

  fun quoteVal m =
    case out m of
       O.V theta $ es => P.$ (theta, List.map quoteB es)
     | _ => raise Fail "Expected value"

  fun quoteCont k =
    case out k of
       O.K theta $ es => P.$ (theta, List.map quoteB es)
     | _ => raise Fail "Expected continuation"


  fun interpret (env as (mrho, srho, vrho)) =
    fn P.RETURN x => x <: env
     | P.SUBST ((x, p), p') =>
         let
           val vrho' = Variable.Ctx.insert vrho x (interpret env p)
         in
           interpret (mrho, srho, vrho') p'
         end
     | P.REN ((u, v), p) =>
         let
           val srho' = Symbol.Ctx.insert srho u v
         in
           interpret (mrho, srho', vrho) p
         end

  fun step (m <: (env as (mrho, srho, vrho))) =
    case out m of
       ` x => SOME @@ Variable.Ctx.lookup vrho x
     | x $# (us, ms) =>
         let
           val e <: (mrho', srho', vrho') = Metavariable.Ctx.lookup mrho x
           val (vs', xs) \ m = outb e
           val srho'' = ListPair.foldlEq  (fn (v,(u, _),r) => Symbol.Ctx.insert r v u) srho' (vs', us)
           val vrho'' = ListPair.foldlEq (fn (x,m,r) => Variable.Ctx.insert r x (m <: (mrho', srho', vrho'))) vrho' (xs, ms)
         in
           raise Match
         end
     | O.C (O.RET sigma) $ _ => NONE
     | O.C (O.CUT (sigma, tau)) $ [_ \ k, _ \ e] =>
         (case step (e <: env) of
             NONE =>
               (case out e of
                   O.C (O.RET sigma) $ [_ \ m] => SOME @@ interpret env (plug (quoteCont k) (quoteVal m))
                 | _ => raise Fail "Expected RET")
           | SOME (e' <: env') => SOME @@ O.C (O.CUT (sigma, tau)) $$ [([],[]) \ k, ([],[]) \ e'] <: env')
     | _ => raise Match
end
