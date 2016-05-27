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



  type control = abt

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

  datatype continuation =
     DONE
   | CONT of abt * environment * continuation

  type machine = control * environment * continuation

  fun step (m, env as (mrho, srho, vrho), cont) : machine =
    case out m of
       `x =>
         let
           val n <: env' = Variable.Ctx.lookup vrho x
         in
           (n, env', cont)
         end
     | _ $# _ => raise Fail "Not implemented"
     | O.C (O.RET sigma) $ [_ \ n] =>
         (case cont of
             CONT (k, env', cont') =>
               let
                 val m' <: env' = interpret env' @@ plug (quoteCont k) (quoteVal n)
               in
                 (m', env', cont')
               end
           | DONE => (m, env, cont))
     | O.C (O.CUT (sigma, tau)) $ [_ \ k, _ \ e] =>
         (e, env, CONT (k, env, cont))
     | _ => raise Fail "Expected command"

    (*
    case out m of
       ` x => cc @@ Variable.Ctx.lookup vrho x
     | x $# (us, ms) =>
         let
           val e <: (mrho', srho', vrho') = Metavariable.Ctx.lookup mrho x
           val (vs', xs) \ m = outb e
           val srho'' = ListPair.foldlEq  (fn (v,(u, _),r) => Symbol.Ctx.insert r v u) srho' (vs', us)
           val vrho'' = ListPair.foldlEq (fn (x,m,r) => Variable.Ctx.insert r x (m <: (mrho', srho', vrho'))) vrho' (xs, ms)
         in
           cc @@ m <: (mrho', srho'', vrho'')
         end
     | O.C (O.RET sigma) $ _ => NONE
     | O.C (O.CUT (sigma, tau)) $ [_ \ k, _ \ e] =>
         (case step (e <: env) (fn x => O.C (O.CUT (sigma, tau)) $$ [([],[]) \ k, ([],[]) \ x]) of
             NONE =>
               (case out e of
                   O.C (O.RET sigma) $ [_ \ m] => SOME @@ interpret env (plug (quoteCont k) (quoteVal m))
                 | _ => raise Fail "Expected RET")
           | SOME (e' <: env') => SOME (e' <: env))
     | _ => raise Match*)
end
