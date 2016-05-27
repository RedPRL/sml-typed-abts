functor LcsDynamics
  (structure Lcs : LCS_DEFINITION
   structure Abt : ABT
     where type 'a Operator.t = 'a Lcs.O.operator
     where type Operator.Arity.Valence.Sort.t = Lcs.O.Sort.t
     where type 'a Operator.Arity.Valence.Spine.t = 'a list) : LCS_DYNAMICS =
struct

  structure Lcs = Lcs and Abt = Abt

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


  structure Closure = LcsClosure (Abt)
  open Closure

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

  infix 1 ||

  fun inject m =
    m <: (Metavariable.Ctx.empty, Symbol.Ctx.empty, Variable.Ctx.empty) || DONE

  (* To take an intermediate state and turn it into a term *)
  fun project (s : expr state) : expr =
    case s of
       cl || DONE => raise Match
     | m <: env || CONT (k <: env' || cont) =>
         let
           val O.Sort.CONT (sigma, tau) = sort k
           val m' = O.C (O.CUT (sigma, tau)) $$ [([],[]) \ force (m <: env), ([],[]) \ k]
         in
           project @@ m' <: env' || cont
         end

  (* I'm not sure this is right, but it seems to be on the right track. It's basically a CEK machine. *)
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

  local
    fun go (cl || DONE) = force cl
      | go st = go (step st)
  in
    val eval : abt -> abt =
      go o inject
  end

end
