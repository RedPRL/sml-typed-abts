

structure IntSet = SplaySet (structure Elem = IntOrdered)

functor PrincipalArguments (type 'a operator) : INSTR =
struct
  type addr = int
  type 'a operator = 'a operator
  type var = unit
  type sym = unit
  type term = unit

  type instr = IntSet.set

  datatype scope = \\ of (int -> var) * term
  infix \\

  fun self k =
    k ()

  val final =
    IntSet.empty

  fun expect (a, theta, k) =
    IntSet.insert (k ((fn _ => ()) \\ ())) a

  fun use (m, theta, k) =
    k ((fn _ => ()) \\ ())

  fun subst (n, x, m, k) =
    k ()

  fun ret m =
    IntSet.empty

  val stuck =
    IntSet.empty

  fun orElse (u, v) =
    IntSet.union u v
end

functor Compile (Abt : ABT where type 'a Operator.Arity.Valence.Spine.t = 'a list) : INSTR =
struct
  open Abt
  infix $ \ $#

  type addr = int
  type 'a operator = 'a Operator.t
  type sym = symbol
  type var = variable
  type term = abt

  type instr = (abt -> abt) -> abt -> abt option
  datatype scope = \\ of (int -> var) * term
  infix \\

  fun self k eval x =
    k x eval x

  fun final x _ =
    NONE

  fun ret n eval m =
    SOME n

  fun toScope ((us, xs) \ m) =
    (fn i => List.nth (xs, i) handle _ => raise Fail "FUCK!") \\ m

  fun matchOperator pat theta =
    Operator.eq
      (fn _ => true)
      (Operator.map (fn _ => ()) theta, pat)

  fun getNthArg i m =
    case out m of
       theta $ es =>
         toScope (List.nth (es, i))
     | _ => raise Fail "Expected operator"

  fun expect (i, pat, k) eval m =
    let
      val e as xs \\ m' = getNthArg i m
      val m'' = eval m'
    in
      case out m'' of
         theta $ es =>
           if matchOperator pat theta then
             k (xs \\ m'') eval m
           else
             raise Fail ("Expected " ^ Operator.toString (fn _ => "-") pat ^ " but got " ^ Operator.toString Symbol.toString theta)
       | _ => raise Fail "Expected operator"
    end

  fun use (n, i, k) eval m =
    k (getNthArg i n) eval m

  fun stuck _ _ =
    raise Fail "STUCK!"

  fun orElse (f, g) eval x =
    f eval x handle _ => g eval x

  fun subst (n2, x, n1, k) eval m =
    k (Abt.subst (n2, x) n1) eval m
end

structure UnitSort : SORT =
struct
  type t = unit
  fun eq _ = true
  fun toString _ = "exp"
end

structure LambdaOperatorData =
struct
  datatype operator = LAM | AP | AX
end

structure LambdaOperator = SimpleOperator
  (struct
    structure Arity = ListArity (UnitSort)
    open LambdaOperatorData

    type t = operator

    fun makeValence n =
      (([], List.tabulate (n, fn _ => ())), ())

    fun makeArity xs =
      (List.map makeValence xs, ())

    val arity =
      fn LAM => makeArity [1]
       | AP => makeArity [0,0]
       | AX => makeArity []

    fun eq (x : t, y) =
      x = y

    val toString =
      fn LAM => "lam"
       | AP => "ap"
       | AX => "ax"
  end)

structure Lambda = SimpleAbt (LambdaOperator)

functor LambdaComputationRepr (I : INSTR where type 'a operator = 'a LambdaOperator.t) =
struct
  open LambdaOperatorData

  open I
  infix \\

  fun get (i, k) =
    self (fn m => use (m, i, k))

  val table =
    fn LAM => final
     | AX => final
     | AP =>
         expect (0, LAM, fn _ \\ lam =>
           use (lam, 0, fn xs \\ mx =>
             get (1, fn _ \\ n =>
               subst (n, xs 0, mx, ret))))
end

signature REDEX_TABLE =
sig
  structure Abt : ABT
  val table : Abt.operator -> (Abt.abt -> Abt.abt) -> Abt.abt -> Abt.abt option
end

signature SMALL_STEP =
sig
  structure Abt : ABT
  val step : Abt.abt -> Abt.abt option
end

functor SmallStep (R : REDEX_TABLE) : SMALL_STEP =
struct
  structure Abt = R.Abt
  open R.Abt
  infix $ \

  structure Show = PlainShowAbt (R.Abt)

  fun step m =
    case out m of
       theta $ _ => R.table theta eval m
     | _ => raise Fail "Stuck!"
  and eval m =
    case step m of
       SOME m' => eval m'
     | NONE => m
end

structure LambdaComputation = LambdaComputationRepr (Compile (Lambda))
structure Welp = SmallStep (structure Abt = Lambda open LambdaComputation)

structure Playground =
struct
  open LambdaOperatorData Lambda
  structure ShowLambda = PlainShowAbt (Lambda)
  infix 5 $ \

  fun $$ (theta, es) = Lambda.check' (theta $ es, ())
  fun `` x = Lambda.check' (`x, ())

  infix 6 $$

  val x = Variable.named "x"

  val id = LAM $$ [([],[x]) \ ``x]
  val ax = AX $$ []
  fun ap m n = AP $$ [([],[]) \ m, ([],[]) \ n]

  val ex1 = ap (ap id id) ax
  val SOME ex1' = Welp.step ex1

  val _ = print ("\n\n" ^ ShowLambda.toString ex1' ^ "\n\n")

    (*
  val ex1 = LAM $ [["x"] \ `"x"]
  val ex2 = AP $ [[] \ ex1, [] \ (AX $ [])]
  *)
end
