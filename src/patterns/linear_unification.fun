functor AbtLinearUnification (P : ABT_PATTERN) : ABT_LINEAR_UNIFICATION =
struct
  open P
  open Abt Pattern

  structure Env =
    SplayDict
      (structure Key =
       struct
         open Abt.Metavariable Abt.Metavariable.Eq
       end)

  type env = abt bview Env.dict
  type renaming = (Abt.symbol * Abt.symbol) list

  exception UnificationFailure

  datatype match = <*> of pattern * abt

  infix $ $# $@ \ <*>
  structure Spine = Operator.Arity.Valence.Spine
  structure Sort = Operator.Arity.Sort

  fun matchOperator (ptheta, theta) =
    (* compare if they are the "same" operator modulo parameters *)
    if Operator.Eq.eq (fn _ => true) (ptheta, theta) then
      let
        (* therefore, the operators should have compatible supports *)
        val us = map #1 (Operator.support ptheta)
        val vs = map #1 (Operator.support theta)
      in
        ListPair.zipEq (us, vs)
      end
    else
      raise UnificationFailure

  fun matchSort (sigma, tau) =
    if Sort.Eq.eq (sigma, tau) then
      ()
    else
      raise UnificationFailure

  fun extendEnv rho (mv, e) =
    Env.insertMerge rho mv e (fn _ => raise UnificationFailure)
  fun concatEnv (rho, rho') =
    Env.union rho rho' (fn _ => raise UnificationFailure)

  fun unify (pat <*> m) : renaming * env =
    let
      val (ptheta $@ pargs, Theta) = Pattern.out pat
      val (theta $ es, tau) = Abt.infer m
      fun go [] [] (rho, env) = (rho, env)
        | go (MVAR mv :: pargs) (e :: es) (rho, env) = go pargs es (rho, extendEnv env (mv, e))
        | go (PAT pat :: pargs) ((([], []) \ m) :: es) (rho, env) =
            let
              val (rho', env') = unify (pat <*> m)
            in
              go pargs es (rho @ rho', concatEnv (env, env'))
            end
        | go _ _ _ = raise UnificationFailure
      val (rho, env) = go pargs es ([], Env.empty)
    in
      (matchOperator (ptheta, theta) @ rho, env)
    end
end
