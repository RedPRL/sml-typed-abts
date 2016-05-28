structure Lambda =
struct
  (* As an example, we give a lambda calculus with strict naturals numbers and strict pairs. *)
  datatype value = LAM | AX | PAIR | NUM of int

  datatype pair_hole = P0 | P1 | P2
  datatype cont = AP | SPREAD | KPAIR of pair_hole | SUC
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
     | NUM i => Ar.make []

  fun eq (x : t, y) = x = y

  val toString =
    fn LAM => "lam"
     | PAIR => "pair"
     | AX => "ax"
     | NUM i => "#" ^ Int.toString i
end

structure LambdaK : ABT_SIMPLE_OPERATOR =
struct
  structure Ar = UnisortedAbtArity

  open Lambda
  type t = Lambda.cont

  val arity =
    fn AP => Ar.make [(0,0)]
     | SPREAD => Ar.make [(0,2)]
     | KPAIR P0 => Ar.make [(0,0), (0,0)]
     | KPAIR P1 => Ar.make [(0,0)]
     | KPAIR P2 => Ar.make [(0,0)]
     | SUC => Ar.make []

  fun eq (theta1 : t, theta2) = theta1 = theta2

  val toString =
    fn AP => "ap"
     | SPREAD => "spread"
     | KPAIR P0 => "pair([_],[_])"
     | KPAIR P1 => "pair(-,[_])"
     | KPAIR P2 => "pair([_],-)"
     | SUC => "S[-]"
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

  fun ret m =
    O.RET () $$ [([],[]) \ m]

  fun plug sign ((v, k) <: env || st) =
    case (v, k) of
       (LAM `$ [(_, [x]) \ mx], AP `$ [_ \ n]) =>
         let
           val env' = pushV (n <: env, x) env
         in
           mx <: env'|| st
         end
     | (PAIR `$ [_ \ m1, _ \ m2], SPREAD `$ [(_, [x,y]) \ nxy]) =>
         let
           val env' = pushV (m1 <: env, x) (pushV (m2 <: env, y) env)
         in
           nxy <: env' || st
         end
     | (_, KPAIR P0 `$ [_ \ m, _ \ n]) =>
         let
           val k = O.K (KPAIR P1) $$ [([],[]) \ n] <: env
         in
           m <: env || k :: st
         end
     | (theta `$ es, KPAIR P1 `$ [_ \ n]) =>
         let
           val m0 = ret (O.V theta $$ es)
           val k = O.K (KPAIR P2) $$ [([],[]) \ m0] <: env
         in
           n <: env || k :: st
         end
     | (theta `$ es, KPAIR P2 `$ [_ \ m0]) =>
         let
           val n0 = ret (O.V theta $$ es)
           val p = ret (O.V PAIR $$ [([],[]) \ m0, ([],[]) \ n0])
         in
           p <: env || st
         end
     | (NUM i `$ _, SUC `$ _) =>
         let
           val n = ret (O.V (NUM (i + 1)) $$ [])
         in
           n <: env || st
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

  val ze = ret (V (NUM 0) $$ [])

  fun suc m =
    cut (K SUC $$ []) m

  fun pair (m, n) =
    cut (K (KPAIR P0) $$ [([],[]) \ m, ([],[]) \ n]) ax

  fun id a =
    let
      val x = Var.named a
    in
      lam (x, check (`x, EXP ()))
    end

  val tm1 = suc (suc (ap (id "a") (ap (id "b") (suc ze))))

  structure Show = DebugShowAbt (Abt)
  val _ = print "\n\n"
  val _ = debugTrace Sig.empty (pair (tm1, tm1))
  val _ = print "\n\n"
end
