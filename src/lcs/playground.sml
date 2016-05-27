structure LambdaVal =
struct
  structure Arity = UnisortedArity
  datatype 'i t = LAM | AX | PAIR

  val arity =
    fn LAM => Arity.make [(0,1)]
     | PAIR => Arity.make [(0,0), (0,0)]
     | AX => Arity.make []

  fun support _ = []

  fun eq _ =
    fn (LAM, LAM) => true
     | (PAIR, PAIR) => true
     | (AX, AX) => true
     | _ => false

  fun toString _ =
    fn LAM => "lam"
     | PAIR => "pair"
     | AX => "ax"

  fun map f =
    fn LAM => LAM
     | PAIR => PAIR
     | AX => AX
end

structure LambdaCont =
struct
  structure Arity = UnisortedArity
  datatype 'i t = AP | SPREAD

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
structure LambdaOperator = LcsOperator (structure Sort = LambdaSort and Val = LambdaVal and Cont = LambdaCont)

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
        raise Fail (LambdaVal.toString (fn _ => "-") theta2)

end

structure LambdaAbt = SimpleAbt (LambdaOperator)
structure LambdaDynamics = LcsDynamics (structure Lcs = LambdaLcs and Abt = LambdaAbt)

structure Test =
struct
  open LambdaVal LambdaCont LambdaSort LambdaOperator LambdaAbt LambdaDynamics

  infix 2 $ $$
  infix 1 \

  fun ap m n =
    C (CUT ((), ())) $$ [([],[]) \ K AP $$ [([],[]) \ n], ([],[]) \ m]

  fun lam (x, m) =
    C (RET ()) $$ [([],[]) \ V LAM $$ [([], [x]) \ m]]

  val ax = C (RET ()) $$ [([],[]) \ V AX $$ []]

  val x = Variable.named "x"
  val tm1 = ap (lam (x, check (`x, CMD ()))) ax
  val tm2 = eval () tm1

  structure Show = DebugShowAbt (LambdaAbt)
  val _ = print (Show.toString tm2 ^ "\n")
end
