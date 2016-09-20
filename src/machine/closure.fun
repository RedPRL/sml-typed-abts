functor AbtClosure (Abt : ABT) : ABT_CLOSURE =
struct
  structure Abt = Abt and Sp = Abt.O.Ar.Vl.Sp and P = Abt.O.P

  type 'a env = {params : Abt.symenv, terms : 'a Abt.Var.Ctx.dict}
  type ('a, 'b) tensor = 'a * 'b env

  datatype ('a, 'b) closure = <: of ('a, ('b, 'b) closure) tensor

  local
    open Abt
    infix 0 <:
    infix 1 $ $$ $# \

    fun map1 f (x, y) = (f x, y)
    fun close env m = m <: env

    fun sym (env : 'a env) a =
      case Sym.Ctx.find (#params env) a of
         SOME p => p
       | NONE => P.ret a
  in
    fun force (tm <: env) =
      case infer tm of
         (`x, tau) =>
           (case Var.Ctx.find (#terms env) x of
               SOME cl => force cl
             | NONE => tm)
       | (x $# (ps, ms), tau) =>
           let
             val ps' = Sp.map (map1 (P.bind (sym env))) ps
             val ms' = Sp.map (force o close env) ms
           in
             setAnnotation (getAnnotation tm) (Abt.check (x $# (ps', ms'), tau))
           end
       | (theta $ es, tau) =>
           let
             val theta' = O.map (sym env) theta
             val es' = Sp.map (mapBind (force o close env)) es
           in
             setAnnotation (getAnnotation tm) (theta' $$ es')
           end

    fun forceParam (p <: env) =
      P.bind (sym env) p
  end
end

functor AbtClosureUtil (Cl : ABT_CLOSURE) : ABT_CLOSURE_UTIL =
struct
  open Cl

  fun insertSym {params, terms} u p =
    {params = Abt.Sym.Ctx.insert params u p,
     terms = terms}

  fun insertVar {params, terms} x t =
    {params = params,
     terms = Abt.Var.Ctx.insert terms x t}
end
