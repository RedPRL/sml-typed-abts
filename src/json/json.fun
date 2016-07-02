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
        (Option.valOf (decodeOperator theta), decodeArguments env ctx args)
     | _ => raise DecodeAbt

  and encodeArguments es =
    J.Array (map encodeB es)

  and decodeArguments env ctx =
    fn J.Array es => map (decodeB env ctx) es
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

  and decodeB (env : env) (ctx : ctx) =
    fn J.Obj [("syms", J.Array syms), ("vars", J.Array vars), ("body", body)] =>
         Abt.\ ((map (decodeSym env) syms, map (decodeVar env) vars), decode env ctx body)
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
