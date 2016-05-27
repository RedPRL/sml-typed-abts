structure Lambda =
struct
  datatype value = LAM | AX | PAIR
  datatype cont = AP | SPREAD
end

structure LambdaVal : SIMPLE_OPERATOR =
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

structure LambdaCont : CONT_OPERATOR =
struct
  structure Arity = UnisortedArity

  type 'i t = Lambda.cont

  open Lambda

  val arity =
    fn AP => Arity.make [(0,0)]
     | SPREAD => Arity.make [(0,2)]

  val input =
    fn AP => ()
     | SPREAD => ()

  fun support _ = []

  fun eq _ =
    fn (AP, AP) => true
     | (SPREAD, SPREAD) => true
     | _ => false

  fun toString _ =
    fn AP => "ap"
     | SPREAD => "spread"

  fun map _ =
    fn AP => AP
     | SPREAD => SPREAD
end


structure LambdaSort = LcsSort (structure AtomicSort = UnisortedValence.Sort val opidSort = NONE)
structure LambdaOperator = LcsOperator (structure Sort = LambdaSort and Val = SimpleOperator(LambdaVal) and Cont = LambdaCont)

structure LambdaLcs : LCS_DEFINITION =
struct
  structure O = LambdaOperator and P = LcsPattern
  open LambdaVal LambdaCont

  type sign = unit

  open P O

  type ('s, 'v, 't) value = ('s, 'v, 's O.Val.t, 't) P.pat
  type ('s, 'v, 't) cont = ('s, 'v, 's O.Cont.t, 't) P.pat

  infix $ \

  nonfix ^
  val ^ = RETURN

  fun plug (AP $ [_ \ n]) (LAM $ [(_, [x]) \ mx]) =
       SUBST ((x, ^ n), ^ mx)
    | plug (SPREAD $ [(_, [x,y]) \ nxy]) (PAIR $ [_ \ m1, _ \ m2])  =
       SUBST ((x, ^ m1), SUBST ((y, ^ m2), ^ nxy))
    | plug (theta1 $ _) (theta2 $ _) =
        raise Fail (LambdaVal.toString theta2)
end

structure LambdaAbt = SimpleAbt (LambdaOperator)
structure LambdaDynamics = LcsDynamics (structure Lcs = LambdaLcs and Abt = LambdaAbt)

structure Test =
struct
  open Lambda LambdaCont LambdaSort LambdaOperator LambdaAbt LambdaDynamics

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

  val x = Variable.named "x"
  val tm1 = ap (lam (x, check (`x, EXP ()))) ax
  val tm2 = eval () tm1

  structure Show = DebugShowAbt (LambdaAbt)
  val _ = print (Show.toString tm2 ^ "\n")
end
