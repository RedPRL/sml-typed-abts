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


structure LambdaSort = LcsSort (UnisortedValence.Sort)
structure LambdaOperator = LcsOperator (structure Sort = LambdaSort and Val = LambdaVal and Cont = LambdaCont)

structure LambdaLcs : LCS_DEFINTION =
struct
  structure O = LambdaOperator and P = LcsPattern
  type sign = unit

  open P O

  type ('s, 'v, 't) value = ('s, 'v, 's O.Val.t, 't) P.pat
  type ('s, 'v, 't) cont = ('s, 'v, 's O.Cont.t, 't) P.pat

  infix $ \

  nonfix ^
  val ^ = RETURN

  fun plug (LAM $ [(_, [x]) \ mx]) (AP $ [_ \ n]) =
       SUBST ((x, ^ n), ^ mx)
    | plug (PAIR $ [_ \ m1, _ \ m2]) (SPREAD $ [(_, [x,y]) \ nxy]) =
       SUBST ((x, ^ m1), SUBST ((y, ^ m2), ^ nxy))
    | plug _ _ = raise Match

end
