structure Lambda =
struct
  (* As an example, we give a lambda calculus with eager natural numbers and eager pairs. *)
  datatype value = LAM | AX | PAIR | NUM of int

  datatype pair_hole = P1 | P2
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
     | KPAIR P1 => Ar.make [(0,0)]
     | KPAIR P2 => Ar.make [(0,0)]
     | SUC => Ar.make []

  fun eq (theta1 : t, theta2) = theta1 = theta2

  val toString =
    fn AP => "ap"
     | SPREAD => "spread"
     | KPAIR P1 => "pair([_],-)"
     | KPAIR P2 => "pair(-,[_])"
     | SUC => "S[-]"
end


structure LambdaLang : LCS_LANGUAGE =
struct
  structure V = AbtSimpleOperator (LambdaV) and K = AbtSimpleOperator (LambdaK) and D = AbtEmptyOperator (UnisortedAbtArity)
  fun input _ = ([], ())
  val opidSort = NONE
end

structure LambdaKit = LcsDynamicsBasisKit (LambdaLang)

structure LambdaBasis : LCS_DYNAMICS_BASIS =
struct
  open Lambda
  open LambdaKit.Abt
  open LambdaKit
  open M M.Cl

  fun @@ (f, x) = f x

  infix @@
  infix 1 <| |>
  infix 3 <:
  infix 3 $ $$ `$
  infix 2 \

  fun pushV (cl : abt closure, x) (mrho, srho, vrho) =
    (mrho, srho, Var.Ctx.insert vrho x cl)

  fun ret m =
    O.RET () $$ [([],[]) \ m]

  fun delta sign _ =
    raise Fail "Impossible"

  fun catch _ _ _ =
    NONE

  fun throw _ =
    raise Fail "unimplemented"

  fun plug sign ((_, v <: env), k) st =
    case (v, k) of
       (LAM `$ [(_, [x]) \ mx], AP `$ [_ \ n]) =>
         let
           val env' = pushV (n, x) env
         in
           mx <: env' <| st
         end
     | (PAIR `$ [_ \ m1, _ \ m2], SPREAD `$ [(_, [x,y]) \ nxy <: env']) =>
         let
           val env'' = pushV (m1 <: env, x) @@ pushV (m2 <: env, y) env'
         in
           nxy <: env'' <| st
         end
     | (pat, KPAIR P1 `$ [_ \ n <: envN]) =>
         let
           val m0 = ret (unquoteV pat)
           val k = KPAIR P2 `$ [([],[]) \ m0 <: env]
         in
           n <: envN <| k :: st
         end
     | (pat, KPAIR P2 `$ [_ \ m0 <: envM0]) =>
         let
           (* TODO: what to do with envM0? *)
           val n0 = ret @@ unquoteV pat
           val p = ret @@ O.V PAIR $$ [([],[]) \ m0, ([],[]) \ n0]
         in
           p <: env <| st
         end
     | (NUM i `$ _, SUC `$ _) =>
         let
           val n = ret @@ O.V (NUM (i + 1)) $$ []
         in
           n <: env <| st
         end
     | _ => raise Fail "Invalid computation"
end

structure LambdaDynamics = LcsDynamics (LambdaBasis)

structure Notation =
struct
  open LambdaKit Lambda LambdaV LambdaK

  local
    open O O.S Abt
    infix 2 $ $$
    infix 1 \
  in
    fun ret m =
      RET () $$ [([],[]) \ m]

    fun cut k e =
      CUT (([],()), ()) $$ [([],[]) \ k, ([],[]) \ e]

    fun ap e1 e2 =
      cut (K AP $$ [([],[]) \ e2]) e1

    fun lam (x, m) =
      ret (V LAM $$ [([],[x]) \ m])

    val ax = ret (V AX $$ [])

    val ze = ret (V (NUM 0) $$ [])

    fun suc m =
      cut (K SUC $$ []) m

    fun pair (m, n) =
      cut (K (KPAIR P1) $$ [([],[]) \ n]) m

    fun id a =
      let
        val x = Var.named a
      in
        lam (x, check (`x, EXP ()))
      end
  end
end

structure Test =
struct
  open LambdaKit LambdaDynamics Notation

  val tm1 = ap (id "c") (suc (suc (ap (id "a") (ap (id "b") (suc ze)))))

  val x = Abt.Var.named "x"
  val xtm = Abt.check (Abt.` x, O.S.EXP ())

  structure Show = DebugShowAbt (Abt)
  val _ =
    (print "\n\n";
     debugTrace Sig.empty (pair (xtm, xtm));
     print "\n\n";
     debugTrace Sig.empty (pair (tm1, suc tm1));
     print "\n\n\n\n")
end
