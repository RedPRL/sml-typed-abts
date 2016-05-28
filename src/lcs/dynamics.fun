functor LcsDynamics (B : LCS_DYNAMICS_BASIS) : LCS_DYNAMICS =
struct
  open B
  structure Abt = M.Cl.Abt and Sig = Sig
  open O O.L Abt M M.Cl

  infix 3 $ $$ $# `$ \ <:
  infix 1 <| |>

  fun @@ (f, x) = f x
  infix 0 @@


  (* To take an intermediate state and turn it into a term *)
  fun run (s : expr state) : expr =
    case s of
       cl |> [] => force cl
     | cl <| [] => force cl
     | m <: env <| ((k <: env') :: stack) =>
         (case sort k of
             B.O.S.CONT (sigma, tau) =>
               let
                 val m' = B.O.CUT (sigma, tau) $$ [([],[]) \ k, ([],[]) \ force (m <: env)]
               in
                 run @@ m' <: env' <| stack
               end
           | _ => raise Fail "Expected continuation sort")
     | m <: env |> ((k <: env') :: stack) =>
         (case sort k of
             B.O.S.CONT (sigma, tau) =>
               let
                 val m' = B.O.CUT (sigma, tau) $$ [([],[]) \ k, ([],[]) \ force (m <: env)]
               in
                 run @@ m' <: env' |> stack
               end
           | _ => raise Fail "Expected continuation sort")

  structure Pattern = Pattern (Abt)
  structure Unify = AbtLinearUnification (structure Abt = Abt and Pattern = Pattern)
  structure SymEnvUtil = ContextUtil (structure Ctx = Sym.Ctx and Elem = Sym)
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
       B.O.K theta $ es => theta `$ es
     | _ => raise Fail "Expected continuation"

  fun quoteV k =
    case out k of
       B.O.V theta $ es => theta `$ es
     | _ => raise Fail "Expected value"

  fun step sign (m <: env <| stack) =
    let
      val (mrho, srho, vrho) = env
    in
      case out m of
         `x => (Var.Ctx.lookup vrho x <| stack handle _ => m <: env |> stack)
       | x $# (us, ms) =>
           let
             val e <: (mrho', srho', vrho') = Metavar.Ctx.lookup mrho x
             val (vs', xs) \ m = outb e
             val srho'' = ListPair.foldlEq  (fn (v,(u, _),r) => Sym.Ctx.insert r v u) srho' (vs', us)
             val vrho'' = ListPair.foldlEq (fn (x,m,r) => Var.Ctx.insert r x (m <: (mrho', srho', vrho'))) vrho' (xs, ms)
           in
             m <: (mrho', srho'', vrho'') <| stack
           end
       | B.O.RET sigma $ [_ \ n] => m <: env |> stack
       | B.O.CUT (sigma, tau) $ [_ \ k, _ \ e] =>
           e <: env <| (k <: env) :: stack
       | B.O.CUSTOM (opid, params, ar) $ _ =>
           let
             open Unify infix <*>
             val def as {definiens, ...} = Sig.lookup sign opid
             val pat = patternFromDef (opid, ar) def

             val (srho', mrho') = unify (pat <*> m)
             val srho'' = SymEnvUtil.union (srho, srho)
             val mrho'' =
               Metavar.Ctx.union mrho
                 (Metavar.Ctx.map (fn e => e <: (mrho, srho, vrho)) mrho')
                 (fn _ => raise Fail "Stuck")
           in
             definiens <: (mrho'', srho'', vrho) <| stack
           end
       | _ => raise Fail "Expected expression"
    end
    | step sign (m <: env |> []) = m <: env |> []
    | step sign (m <: env |> (k <: env') :: stack) =
        let
          (* If we are in |> mode, then we may assume that we have got either
             a value or a neutral term. If the former, then [tryPlug] will use the
             client-provided dynamics basis to plug the value into the continuation;
             if [tryPlug] fails, this means we have a "stuck term". If the term is
             either neutral or stuck, we will re-wrap it in the continuation and continue
             working our way through the stack. *)
          fun tryPlug () =
            case out m of
               B.O.RET sigma $ [_ \ n] => B.plug sign ((quoteV n, quoteK k) <: env') stack
             | _ => raise Fail "Expected value"
        in
          tryPlug () handle _ =>
            (case sort k of
                B.O.S.CONT (sigma, tau) => B.O.CUT (sigma, tau) $$ [([],[]) \ k, ([],[]) \ m] <: env' |> stack
              | _ => raise Fail "Expected continuation sort")
        end

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
