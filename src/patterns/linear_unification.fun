functor AbtLinearUnification (P : ABT_PATTERN) : ABT_LINEAR_UNIFICATION =
struct
  open P
  open Abt Pattern

  exception UnificationFailure

  datatype match = <*> of pattern * abt

  infix $ $# $@ \ <*>
  structure Vl = O.Ar.Vl
  structure Sp = Vl.Sp and S = Vl.S
  structure SymCtx = Sym.Ctx and MetaCtx = Metavar.Ctx

  fun matchOperator (ptheta, theta) =
    (* compare if they are the "same" operator modulo parameters *)
    if O.eq (fn _ => true) (ptheta, theta) then
      let
        (* therefore, the operators should have compatible supports *)
        val us = O.support ptheta
        val vs = O.support theta
      in
        ListPair.foldlEq (fn ((u, _), (v, _), rho) => SymCtx.insert rho u (O.P.pure v)) SymCtx.empty (us, vs)
      end
    else
      raise UnificationFailure

  fun matchSort (sigma, tau) =
    if S.eq (sigma, tau) then
      ()
    else
      raise UnificationFailure

  local
    structure Elem =
    struct
      type t = symbol O.P.t
      val eq = O.P.eq Sym.eq
    end
  in
    structure SymEnvUtil = ContextUtil (structure Ctx = SymCtx and Elem = Elem)
  end

  fun extendEnv rho (mv, e) =
    MetaCtx.insertMerge rho mv e (fn _ => raise UnificationFailure)
  fun concatEnv (rho, rho') =
    MetaCtx.union rho rho' (fn _ => raise UnificationFailure)

  fun concatRen (rho, rho') =
    SymEnvUtil.union (rho, rho')
      handle _ => raise UnificationFailure

  fun asApp m =
    case Abt.out m of
       theta $ es => (theta, es)
     | _ => raise Fail "Expected application"


  fun unify (pat <*> m) : symenv * metaenv =
    let
      val (ptheta $@ pargs, psi) = Pattern.out pat
      val (theta, es) = asApp m
      val (vls, _) = Abt.O.arity theta
      fun go [] ([], []) (rho, env) = (rho, env)
        | go (MVAR mv :: pargs) (e :: es, vl :: vls) (rho, env) =
            let
              val _ \ m = e
            in
              go pargs (es, vls) (rho, extendEnv env (mv, checkb (e,vl)))
            end
        | go (PAT pat :: pargs) ((([], []) \ m) :: es, vl :: vls) (rho, env) =
            let
              val (rho', env') = unify (pat <*> m)
            in
              go pargs (es, vls) (concatRen (rho, rho'), concatEnv (env, env'))
            end
        | go _ _ _ = raise UnificationFailure
      val (rho, env) = go pargs (es, vls) (SymCtx.empty, MetaCtx.empty)
    in
      (concatRen (matchOperator (ptheta, theta), rho), env)
    end
end
