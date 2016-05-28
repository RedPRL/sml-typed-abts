functor Instructions (structure P : LCS_PATTERN and Cl : LCS_CLOSURE) =
struct
  open Cl
  open Abt

  infix <:

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
end

functor LcsDynamics
  (structure O : LCS_OPERATOR
   structure Abt : ABT
     where type 'a Operator.t = 'a O.operator
     where type 'a Operator.Arity.Valence.Spine.t = 'a list
     where type Operator.Arity.Valence.Sort.t = O.Sort.t
   structure Sig : LCS_SIGNATURE where type valence = O.L.V.Arity.Valence.t
   sharing type Sig.symbol = Abt.Symbol.t
   sharing type Sig.metavariable = Abt.Metavariable.t
   sharing type Sig.sort = O.Sort.AtomicSort.t
   sharing type Sig.term = Abt.abt) : LCS_DYNAMICS =
struct
  open O
  structure L = L and Abt = Abt and Sig = Sig

  open L Abt
  infix 3 <:
  infix 3 $ $$ $# \

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

  structure Cl = LcsClosure (Abt)
  structure M =
    LcsMachine
      (structure Cl = Cl
       fun isFinal m =
         case out m of
            O.RET _ $ _ => true
          | _ => false)

  structure I = Instructions (structure P = P and Cl = Cl)
  open Cl M
  infix 1 ||

  (* To take an intermediate state and turn it into a term *)
  fun run (s : expr state) : expr =
    case s of
       cl || [] => force cl
     | m <: env || ((k <: env') :: stack) =>
         let
           val O.Sort.CONT (sigma, tau) = sort k
           val m' = O.CUT (sigma, tau) $$ [([],[]) \ k, ([],[]) \ force (m <: env)]
         in
           run @@ m' <: env' || stack
         end

  structure Pattern = Pattern (Abt)
  structure Unify = AbtLinearUnification (structure Abt = Abt and Pattern = Pattern)
  structure SymEnvUtil = ContextUtil (structure Ctx = Symbol.Ctx and Elem = Symbol)
  structure AbsEq = struct type t = Abt.abs val eq = Abt.eqAbs end

  fun patternFromDef (opid, arity) (def : Sig.def) : Pattern.pattern =
    let
      open Pattern infix 2 $@
      val {parameters, arguments, ...} = def
      val theta = CUSTOM (opid, parameters, arity)
    in
      into @@ theta $@ List.map (fn (x,_) => MVAR x) arguments
    end


  (* I'm not sure this is right, but it seems to be on the right track. It's basically a CEK machine. *)
  fun step sign (m <: (env as (mrho, srho, vrho)) || stack) : expr state =
    case out m of
       `x => Variable.Ctx.lookup vrho x || stack
     | x $# (us, ms) =>
         let
           val e <: (mrho', srho', vrho') = Metavariable.Ctx.lookup mrho x
           val (vs', xs) \ m = outb e
           val srho'' = ListPair.foldlEq  (fn (v,(u, _),r) => Symbol.Ctx.insert r v u) srho' (vs', us)
           val vrho'' = ListPair.foldlEq (fn (x,m,r) => Variable.Ctx.insert r x (m <: (mrho', srho', vrho'))) vrho' (xs, ms)
         in
           m <: (mrho', srho'', vrho'') || stack
         end
     | O.RET sigma $ [_ \ n] =>
         (case stack of
             (k <: env') :: stack' => I.interpret env' (plug (quoteCont k) (quoteVal n)) || stack'
           | [] => m <: env || [])
     | O.CUT (sigma, tau) $ [_ \ k, _ \ e] =>
         e <: env || (k <: env) :: stack
     | O.CUSTOM (opid, params, ar) $ _ =>
         let
           open Unify infix <*>
           val def as {definiens, ...} = Sig.lookup sign opid
           val pat = patternFromDef (opid, ar) def

           val (srho', mrho') = unify (pat <*> m)
           val srho'' = SymEnvUtil.union (srho, srho)
           val mrho'' =
             Metavariable.Ctx.union mrho
               (Metavariable.Ctx.map (fn e => e <: (mrho, srho, vrho)) mrho')
               (fn _ => raise Fail "Stuck")
         in
           definiens <: (mrho'', srho'', vrho) || stack
         end
     | _ => raise Fail "Expected expression"

  fun eval sign =
    run
      o star (step sign)
      o start

  fun debugTrace sign m =
    let
      fun debugStep s =
        let
          val s' = step sign s
          val _ = print @@ M.toString s' ^ "\n"
        in
          s'
        end
      val s0 = start m
    in
      print @@ M.toString s0 ^ "\n";
      star debugStep s0;
      ()
    end

end
