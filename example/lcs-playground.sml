structure Lambda =
struct
  datatype value = LAM | AX | PAIR
  datatype cont = AP | SPREAD
end

structure LambdaV : SIMPLE_OPERATOR =
struct
  structure Arity = UnisortedArity

  open Lambda
  type t = Lambda.value

  val arity =
    fn LAM => Arity.make [(0,1)]
     | PAIR => Arity.make [(0,0), (0,0)]
     | AX => Arity.make []

  fun eq (x : t, y) = x = y

  val toString =
    fn LAM => "lam"
     | PAIR => "pair"
     | AX => "ax"
end

structure LambdaK : SIMPLE_OPERATOR =
struct
  structure Arity = UnisortedArity

  open Lambda
  type t = Lambda.cont

  val arity =
    fn AP => Arity.make [(0,0)]
     | SPREAD => Arity.make [(0,2)]

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
  structure V = SimpleOperator (LambdaV) and K = SimpleOperator (LambdaK) and P = LcsPattern
  open Lambda LambdaV LambdaK P

  type sign = unit

  type ('s, 'v, 't) value = ('s, 'v, 's V.t, 't) P.pat
  type ('s, 'v, 't) cont = ('s, 'v, 's K.t, 't) P.pat

  infix $ \

  nonfix ^
  val ^ = RETURN

  fun input _ = ()

  val opidSort =
    NONE

  fun plug (AP $ [_ \ n]) (LAM $ [(_, [x]) \ mx]) =
       SUBST ((x, ^ n), ^ mx)
    | plug (SPREAD $ [(_, [x,y]) \ nxy]) (PAIR $ [_ \ m1, _ \ m2])  =
       SUBST ((x, ^ m1), SUBST ((y, ^ m2), ^ nxy))
    | plug (theta1 $ _) (theta2 $ _) =
        raise Fail (LambdaV.toString theta2)
end

structure LambdaFramework = LcsFramework (LambdaLang)

structure Test =
struct
  open LambdaFramework
  open Lambda LambdaV LambdaK Dynamics
  open Operator Sort Abt

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
      val x = Variable.named a
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
