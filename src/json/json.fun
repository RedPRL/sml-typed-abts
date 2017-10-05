functor AbtJson (Kit : ABT_JSON_KIT) : ABT_JSON =
struct
  open Kit
  exception DecodeAbt of string

  structure J = Json
  structure NameEnv = SplayDict (structure Key = StringOrdered)

  type env = Abt.metavariable NameEnv.dict * Abt.variable NameEnv.dict
  type ctx = Abt.metactx * Abt.varctx

  val encodeMetavar =
    J.String o Abt.Metavar.toString

  val encodeVar =
    J.String o Abt.Var.toString

  fun decodeMetavar (rho, _) =
    fn J.String u => (NameEnv.lookup rho u handle _ => raise DecodeAbt ("Metavar " ^ u ^ " not in environment"))
     | m => raise DecodeAbt ("Metavar: expected String, but got " ^ J.toString m)

  fun decodeVar (_, rho) =
    fn J.String u => (NameEnv.lookup rho u handle _ => raise DecodeAbt ("Var " ^ u ^ " not in environment"))
     | m => raise DecodeAbt ("Var: expected String, but got " ^ J.toString m)

  fun encodeApp (theta, es) =
    J.Obj
      [("op", encodeOperator theta),
       ("args", encodeArguments es)]

  and decodeApp (env : env) (ctx : ctx) =
    fn J.Obj [("op", theta), ("args", J.Array args)] =>
        let
          val theta = Option.valOf (decodeOperator theta) handle _ => raise DecodeAbt ("Failed to decode operator " ^ J.toString theta)
          val (vls, _) = Abt.O.arity theta
        in
          (theta, decodeArguments env ctx vls args)
        end
     | m => raise DecodeAbt ("App: failed to decode " ^ J.toString m)

  and encodeArguments es =
    J.Array (map encodeB es)

  and decodeArguments (env : env) (ctx : ctx) vls es =
    ListPair.map (fn (e, vl) => decodeB env ctx vl e) (es, vls)

  and encodeMetaApp (x, ms) =
    J.Obj
      [("metavar", encodeMetavar x),
       ("args", J.Array (map encode ms))]

  and decodeMetaApp (env : env) (ctx : ctx) =
    fn J.Obj [("metavar", metavar), ("args", J.Array args)] =>
         (decodeMetavar env metavar,
          map (decode env ctx) args)
     | m => raise DecodeAbt ("MetaApp: failed to decode " ^ J.toString m)

  and encodeB (Abt.\ (xs, m)) =
    J.Obj
      [("vars", J.Array (map encodeVar xs)),
       ("body", encode m)]

  and decodeB (env : env) (ctx : ctx) valence =
    fn J.Obj [("vars", J.Array vars), ("body", body)] =>
         let
           val getStr =
             fn J.String a => a
              | m => raise DecodeAbt ("Expected String but got " ^ J.toString m)

           val (vsorts, _) = valence
           val xs = map (Abt.Var.named o getStr) vars

           val (menv, venv) = env
           val venv' = foldl (fn (x, r) => NameEnv.insert r (Abt.Var.toString x) x) venv xs
           val env' = (menv, venv')

           val (mctx, vctx) = ctx
           val vctx' = ListPair.foldl (fn (x, sigma, r) => Abt.Var.Ctx.insert r x sigma) vctx (xs, vsorts)

           val ctx' = (mctx, vctx')
         in
           Abt.\ (xs, decode env' ctx' body)
         end
     | m => raise DecodeAbt ("Binding: failed to decode " ^ J.toString m)

  and encode m =
    case Abt.out m of
       Abt.`x => J.Obj [("Var", encodeVar x)]
     | Abt.$ (theta, es) => J.Obj [("App", encodeApp (theta, es))]
     | Abt.$# (x, ms) => J.Obj [("MetaApp", encodeMetaApp (x, ms))]

  and decode (env : env) (ctx as (mctx, vctx) : ctx) =
    fn J.Obj [("Var", var)] =>
         let
           val x = decodeVar env var
         in
           Abt.check (Abt.` x, Abt.Var.Ctx.lookup vctx x)
         end
     | J.Obj [("App", app)] => Abt.$$ (decodeApp env ctx app)
     | J.Obj [("MetaApp", app)] =>
         let
           val (x, ms) = decodeMetaApp env ctx app
           val (_, tau) : Abt.valence = Abt.Metavar.Ctx.lookup mctx x
         in
           Abt.check (Abt.$# (x, ms), tau)
         end
     | m => raise DecodeAbt ("Abt: failed to decode " ^ J.toString m)
end
