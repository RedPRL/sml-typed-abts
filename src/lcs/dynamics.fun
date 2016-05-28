functor LcsDynamics (B : LCS_DYNAMICS_BASIS) : LCS_DYNAMICS =
struct
  open B
  structure Abt = M.Cl.Abt and Sig = Sig
  open O O.L Abt M M.Cl

  infix 3 $ $$ $# `$ \ <:
  infix 1 ||

  fun @@ (f, x) = f x
  infix 0 @@


  (* To take an intermediate state and turn it into a term *)
  fun run (s : expr state) : expr =
    case s of
       cl || [] => force cl
     | m <: env || ((k <: env') :: stack) =>
         (case sort k of
             O.Sort.CONT (sigma, tau) =>
               let
                 val m' = O.CUT (sigma, tau) $$ [([],[]) \ k, ([],[]) \ force (m <: env)]
               in
                 run @@ m' <: env' || stack
               end
           | _ => raise Fail "Expected continuation sort")

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


  fun quoteK k =
    case out k of
       O.K theta $ es => theta `$ es
     | _ => raise Fail "Expected continuation"

  fun quoteV k =
    case out k of
       O.V theta $ es => theta `$ es
     | _ => raise Fail "Expected value"

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
             (k <: env') :: stack' => B.plug sign @@ (quoteV n, quoteK k) <: env' || stack'
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
