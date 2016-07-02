functor AbtJson (Kit : ABT_JSON_KIT) : ABT_JSON =
struct
  open Kit
  exception DecodeAbt

  structure J = Json
  structure NameEnv = SplayDict (structure Key = StringOrdered)

  type env = Abt.metavariable NameEnv.dict * Abt.symbol NameEnv.dict * Abt.variable NameEnv.dict
  type ctx = Abt.metactx * Abt.symctx * Abt.varctx

  val encodeMetavar =
    J.String o Abt.Metavar.toString

  val encodeVar =
    J.String o Abt.Var.toString

  val encodeSym =
    J.String o Abt.Sym.toString

  fun decodeMetavar (rho, _, _) =
    fn J.String u => NameEnv.lookup rho u
     | _ => raise DecodeAbt

  fun decodeVar (_, _, rho) =
    fn J.String u => NameEnv.lookup rho u
     | _ => raise DecodeAbt

  fun decodeSym (_, rho, _) =
    fn J.String u => NameEnv.lookup rho u
     | _ => raise DecodeAbt

  fun encodeSymAnn (u, sigma) =
    J.Obj
      [("sym", encodeSym u),
       ("sort", encodeSort sigma)]

  fun decodeSymAnn env =
    fn J.Obj [("sym", u), ("sort", sigma)] => (decodeSym env u, Option.valOf (decodeSort u))
     | _ => raise DecodeAbt

  fun encodeApp (theta, es) =
    J.Obj
      [("op", encodeOperator theta),
       ("args", encodeArguments es)]

  and decodeApp env ctx =
    fn J.Obj [("op", theta), ("args", args)] =>
        let
          val theta = Option.valOf (decodeOperator theta)
          val (vls, _) = Abt.O.arity theta
        in
          (theta, decodeArguments env ctx vls args)
        end
     | _ => raise DecodeAbt

  and encodeArguments es =
    J.Array (map encodeB es)

  and decodeArguments env ctx vls =
    fn J.Array es => ListPair.map (fn (e, vl) => decodeB env ctx vl e) (es, vls)
     | _ => raise DecodeAbt

  and encodeMetaApp (x, us, ms) =
    J.Obj
      [("metavar", encodeMetavar x),
       ("syms", J.Array (map encodeSymAnn us)),
       ("args", J.Array (map encode ms))]

  and decodeMetaApp env ctx =
    fn J.Obj [("metavar", metavar), ("syms", J.Array syms), ("args", J.Array args)] =>
         (decodeMetavar env metavar,
          map (decodeSymAnn env) syms,
          map (decode env ctx) args)
     | _ => raise DecodeAbt

  and encodeB (Abt.\ ((us, xs), m)) =
    J.Obj
      [("syms", J.Array (map encodeSym us)),
       ("vars", J.Array (map encodeVar xs)),
       ("body", encode m)]

  and decodeB (env : env) (ctx : ctx) valence =
    fn J.Obj [("syms", J.Array syms), ("vars", J.Array vars), ("body", body)] =>
         let
           val getStr =
             fn J.String a => a
              | _ => raise DecodeAbt

           val ((ssorts, vsorts), _) = valence
           val us = map (Abt.Sym.named o getStr) syms
           val xs = map (Abt.Var.named o getStr) vars

           val (menv, senv, venv) = env
           val senv' = foldl (fn (u, r) => NameEnv.insert r (Abt.Sym.toString u) u) senv us
           val venv' = foldl (fn (x, r) => NameEnv.insert r (Abt.Var.toString x) x) venv xs
           val env' = (menv, senv', venv')

           val (mctx, sctx, vctx) = ctx
           val sctx' = ListPair.foldl (fn (u, sigma, r) => Abt.Sym.Ctx.insert r u sigma) sctx (us, ssorts)
           val vctx' = ListPair.foldl (fn (x, sigma, r) => Abt.Var.Ctx.insert r x sigma) vctx (xs, vsorts)

           val ctx' = (mctx, sctx', vctx')
         in
           Abt.\ ((us, xs), decode env' ctx' body)
         end
     | _ => raise DecodeAbt

  and encode m =
    case Abt.out m of
       Abt.`x => J.Obj [("Var", encodeVar x)]
     | Abt.$ (theta, es) => J.Obj [("App", encodeApp (theta, es))]
     | Abt.$# (x, (us, ms)) => J.Obj [("MetaApp", encodeMetaApp (x, us, ms))]

  and decode (env : env) (ctx as (mctx, sctx, vctx)) =
    fn J.Obj [("Var", var)] =>
         let
           val x = decodeVar env var
         in
           Abt.check (Abt.` x, Abt.Var.Ctx.lookup vctx x)
         end
     | J.Obj [("App", app)] => Abt.$$ (decodeApp env ctx app)
     | J.Obj [("MetaApp", app)] =>
         let
           val (x, us, ms) = decodeMetaApp env ctx app
           val (_, tau) : Abt.valence = Abt.Metavar.Ctx.lookup mctx x
         in
           Abt.check (Abt.$# (x, (us, ms)), tau)
         end
     | _ => raise DecodeAbt
end
