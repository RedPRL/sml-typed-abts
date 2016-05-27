functor LcsDynamics
  (structure Lcs : LCS_DEFINITION
   structure Abt : ABT
     where type 'a Operator.t = 'a Lcs.O.operator
     where type 'a Operator.Arity.Valence.Spine.t = 'a list) : LCS_DYNAMICS =
struct

  structure Lcs = Lcs

  open Lcs Abt
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



  datatype 'a closure = <: of 'a * environment
  withtype environment = abs closure Metavariable.Ctx.dict * symbol Symbol.Ctx.dict * abt closure Variable.Ctx.dict

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

  type expr = abt
  type cont = abt

  datatype continuation =
     DONE
   | CONT of cont state

  and 'a state = || of 'a closure * continuation

  infix ||

  fun step (m <: (env as (mrho, srho, vrho)) || cont) : expr state =
    case out m of
       `x => Variable.Ctx.lookup vrho x || cont
     | x $# (us, ms) =>
         let
           val e <: (mrho', srho', vrho') = Metavariable.Ctx.lookup mrho x
           val (vs', xs) \ m = outb e
           val srho'' = ListPair.foldlEq  (fn (v,(u, _),r) => Symbol.Ctx.insert r v u) srho' (vs', us)
           val vrho'' = ListPair.foldlEq (fn (x,m,r) => Variable.Ctx.insert r x (m <: (mrho', srho', vrho'))) vrho' (xs, ms)
         in
           m <: (mrho', srho'', vrho'') || cont
         end
     | O.C (O.RET sigma) $ [_ \ n] =>
         (case cont of
             CONT (k <: env' || cont') => interpret env' (plug (quoteCont k) (quoteVal n)) || cont'
           | DONE => m <: env || cont)
     | O.C (O.CUT (sigma, tau)) $ [_ \ k, _ \ e] =>
         e <: env || CONT (k <: env || cont)
     | _ => raise Fail "Expected command"
end
