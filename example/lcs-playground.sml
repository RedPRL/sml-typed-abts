structure Lambda =
struct
  datatype value = LAM | AX | PAIR
  datatype cont = AP | SPREAD
end

structure LambdaV : ABT_SIMPLE_OPERATOR =
struct
  structure Ar = UnisortedAbtArity

  open Lambda
  type t = Lambda.value

  val arity =
    fn LAM => Ar.make [(0,1)]
     | PAIR => Ar.make [(0,0), (0,0)]
     | AX => Ar.make []

  fun eq (x : t, y) = x = y

  val toString =
    fn LAM => "lam"
     | PAIR => "pair"
     | AX => "ax"
end

structure LambdaK : ABT_SIMPLE_OPERATOR =
struct
  structure Ar = UnisortedAbtArity

  open Lambda
  type t = Lambda.cont

  val arity =
    fn AP => Ar.make [(0,0)]
     | SPREAD => Ar.make [(0,2)]

  val eq =
    fn (AP, AP) => true
     | (SPREAD, SPREAD) => true
     | _ => false

  val toString =
    fn AP => "ap"
     | SPREAD => "spread"
end


structure LambdaLang : LCS_LANGUAGE =
struct
  structure V = AbtSimpleOperator (LambdaV) and K = AbtSimpleOperator (LambdaK)
  fun input _ = ()
  val opidSort = NONE
end

structure LambdaKit = LcsDynamicsBasisKit (LambdaLang)

structure LambdaBasis : LCS_DYNAMICS_BASIS =
struct
  open Lambda
  open LambdaKit.Abt
  open LambdaKit
  open M M.Cl

  infix 1 ||
  infix 2 <:
  infix 3 $ $$ `$
  infix 2 \

  fun pushV (cl : abt closure, x) (mrho, srho, vrho) =
    (mrho, srho, Var.Ctx.insert vrho x cl)

  fun plug sign ((v, k) <: env || st) =
    case (v, k) of
       (LAM `$ [ (_, [x]) \ mx ], AP `$ [ _ \ n ]) =>
         let
           val env' = pushV (n <: env, x) env
         in
           mx <: env'|| st
         end
     | (PAIR `$ [ _ \ m1, _ \ m2 ], SPREAD `$ [ (_, [x,y]) \ nxy ]) =>
         let
           val env' = pushV (m1 <: env, x) (pushV (m2 <: env, y) env)
         in
           nxy <: env'|| st
         end
     | _ => raise Fail "Invalid computation"
end

structure LambdaDynamics = LcsDynamics (LambdaBasis)

structure Test =
struct
  open LambdaKit LambdaDynamics
  open Lambda LambdaV LambdaK
  open O O.S Abt

  infix 2 $ $$
  infix 1 \

  fun ret m =
    RET () $$ [([],[]) \ m]

  fun cut k e =
    CUT ((), ()) $$ [([],[]) \ k, ([],[]) \ e]

  fun ap e1 e2 =
    cut (K AP $$ [([],[]) \ e2]) e1

  fun lam (x, m) =
    ret (V LAM $$ [([],[x]) \ m])

  val ax = ret (V AX $$ [])

  fun id a =
    let
      val x = Var.named a
    in
      lam (x, check (`x, EXP ()))
    end

  val tm1 = ap (id "a") (ap (id "b") ax)
  val tm2 = eval Sig.empty tm1

  structure Show = DebugShowAbt (Abt)
  val _ = print "\n\n"
  val _ = debugTrace Sig.empty tm1
  val _ = print "\n\n"
end
