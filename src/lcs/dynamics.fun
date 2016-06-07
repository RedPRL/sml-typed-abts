functor LcsDynamics (B : LCS_DYNAMICS_BASIS) : LCS_DYNAMICS =
struct
  open B
  structure Abt = M.Cl.Abt and Sig = Sig
  open O O.L Abt M M.Cl

  infix 3 $ $$ $# `$ \ <:
  infix 1 <| |>

  fun @@ (f, x) = f x
  infix 0 @@

  fun unquote (theta `$ cls) =
    theta $$ List.map (fn bs \ cl => bs \ force cl) cls

  fun unquoteK ((theta `$ cls) : cont) =
    B.O.K theta $$ List.map (fn bs \ cl => bs \ force cl) cls

  fun quoteK k =
    case out k of
       B.O.K theta $ es => theta `$ es
     | _ => raise Fail "Expected continuation"

  fun quoteV k =
    case out k of
       B.O.V theta $ es => theta `$ es
     | _ => raise Fail "Expected value"

  (* To take an intermediate state and turn it into a term *)
  fun run (s : expr state) : expr =
    case s of
       cl |> [] => force cl
     | cl <| [] => force cl
     | m <: env <| (k :: stack) =>
         let
           val k' = unquoteK k
         in
           case sort k' of
              B.O.S.CONT (sigma, tau) =>
                let
                  val m' = B.O.CUT (sigma, tau) $$ [([],[]) \ unquoteK k, ([],[]) \ force (m <: env)]
                in
                  run @@ m' <: env <| stack
                end
            | _ => raise Fail "Expected continuation sort"
         end
     | m <: env |> (k :: stack) =>
         let
           val k' = unquoteK k
         in
           case sort k' of
              B.O.S.CONT (sigma, tau) =>
                let
                  val m' = B.O.CUT (sigma, tau) $$ [([],[]) \ unquoteK k, ([],[]) \ force (m <: env)]
                in
                  run @@ m' <: env |> stack
                end
            | _ => raise Fail "Expected continuation sort"
         end

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


  fun step sign (st as (m <: env <| stack)) =
    let
      val _ = print @@ M.toString st ^ "\n"
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
       | B.O.D theta $ es =>
           B.delta sign (theta `$ es <: env) <| stack
       | B.O.CUT (sigma, tau) $ [_ \ k, _ \ e] =>
           let
             val theta `$ es = quoteK k
             val k' = theta `$ List.map (fn bs \ m => bs \ (m <: env)) es
           in
             e <: env <| k' :: stack
           end
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
    | step sign (st as (m <: env |> [])) =
      let
        val _ = print @@ M.toString st ^ "\n"
      in
        m <: env |> []
      end
    | step sign (st as (m <: env |> k :: stack)) =
        let
          (* If we are in |> mode, then we may assume that we have got either
             a value or a neutral term. If the former, then [tryPlug] will use the
             client-provided dynamics basis to plug the value into the continuation;
             if [tryPlug] fails, this means we have a "stuck term". If the term is
             either neutral or stuck, we will re-wrap it in the continuation and continue
             working our way through the stack. *)
          fun tryPlug () =
            case out m of
               B.O.RET sigma $ [_ \ n] => B.plug sign (quoteV n <: env, k) stack
             | _ => raise Fail "Expected value"
        in
          tryPlug ()
          handle _ =>
            let
              val k' = unquoteK k
            in
              (case sort k' of
                  B.O.S.CONT (sigma, tau) => B.O.CUT (sigma, tau) $$ [([],[]) \ k', ([],[]) \ m] <: env |> stack
                | _ => raise Fail "Expected continuation sort")
            end
        end

  fun eval sign =
    run
      o star (step sign)
      o start

  fun stepN sign i =
    let
      fun go 0 m = m
        | go i m = go (i - 1) (step sign m)
    in
      run o go i o start
    end

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
