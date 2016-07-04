functor AbtJson (Kit : ABT_JSON_KIT) : ABT_JSON =
struct
  open Kit
  exception DecodeAbt of string

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
    fn J.String u => (NameEnv.lookup rho u handle _ => raise DecodeAbt ("Metavar " ^ u ^ " not in environment"))
     | m => raise DecodeAbt ("Metavar: expected String, but got " ^ J.toString m)

  fun decodeVar (_, _, rho) =
    fn J.String u => (NameEnv.lookup rho u handle _ => raise DecodeAbt ("Var " ^ u ^ " not in environment"))
     | m => raise DecodeAbt ("Var: expected String, but got " ^ J.toString m)

  fun decodeSym (_, rho, _) =
    fn J.String u => (NameEnv.lookup rho u handle _ => raise DecodeAbt ("Sym " ^ u ^ " not in environment"))
     | m => raise DecodeAbt ("Sym: expected String, but got " ^ J.toString m)

  fun encodeSymAnn (u, sigma) =
    J.Obj
      [("sym", encodeSym u),
       ("sort", encodeSort sigma)]

  fun decodeSymAnn env =
    fn J.Obj [("sym", u), ("sort", sigma)] =>
         (decodeSym env u,
          Option.valOf (decodeSort u)
            handle _ => raise DecodeAbt ("Failed to decode sort " ^ J.toString sigma))
     | m => raise DecodeAbt ("SymAnn: failed to decode " ^ J.toString m)

  fun encodeApp (theta, es) =
    J.Obj
      [("op", encodeOperator encodeSym theta),
       ("args", encodeArguments es)]

  and decodeApp env ctx =
    fn J.Obj [("op", theta), ("args", J.Array args)] =>
        let
          val theta = Option.valOf (decodeOperator (SOME o decodeSym env) theta) handle _ => raise DecodeAbt ("Failed to decode operator " ^ J.toString theta)
          val (vls, _) = Abt.O.arity theta
        in
          (theta, decodeArguments env ctx vls args)
        end
     | m => raise DecodeAbt ("App: failed to decode " ^ J.toString m)

  and encodeArguments es =
    J.Array (map encodeB es)

  and decodeArguments env ctx vls es =
    ListPair.map (fn (e, vl) => decodeB env ctx vl e) (es, vls)

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
     | m => raise DecodeAbt ("MetaApp: failed to decode " ^ J.toString m)

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
              | m => raise DecodeAbt ("Expected String but got " ^ J.toString m)

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
     | m => raise DecodeAbt ("Binding: failed to decode " ^ J.toString m)

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
     | m => raise DecodeAbt ("Abt: failed to decode " ^ J.toString m)
end
