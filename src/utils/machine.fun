functor AbtMachine (B : ABT_MACHINE_BASIS) : ABT_MACHINE =
struct
  open B B.M B.M.Cl B.M.Cl.Abt

  infix <: \ `$ $ $# $$

  val emptyEnv = {params = Sym.Ctx.empty, terms = Var.Ctx.empty}

  fun load t =
    (DOWN, t <: emptyEnv, [])

  fun getFirstMatch f =
    fn [] => raise Fail "No match"
     | x :: xs => (case f x of SOME y => y | _ => getFirstMatch f xs)

  fun getHole (_ `$ args) =
    List.foldl (fn _ => raise Match) NONE args

  fun mapPlus f =
    fn HOLE => HOLE
     | % m => % (f m)

  fun close env m =
    m <: env

  fun makeFrame env (k as th `$ args) =
    let
      val (us, xs) = getFirstMatch (fn bs \ HOLE => SOME bs | _ => NONE) args
      fun rho a =
        case Sym.Ctx.find (#params env) a of
           SOME p => p
         | NONE => O.P.pure a
      val th' = O.map rho th
      val args' = List.map (mapBind (mapPlus (close env))) args
    in
      (th' `$ args', (us, xs))
    end

  fun down (foc as t <: env, stk) =
    case out t of
       `x =>
         (case Var.Ctx.find (#terms env) x of
             SOME foc' => (DOWN, foc', stk)
           | NONE => (UNLOAD, foc, stk))
     | _ $# _ => (UNLOAD, foc, stk)
     | th $ args =>
         (case step (th `$ args <: env) of
             STEP foc' => (DOWN, foc', stk)
           | VAL => (UP, foc, stk)
           | CUT ((k, t) <: env) => (DOWN, t <: env, makeFrame env k :: stk))

  fun up (foc, stk) =
    case stk of
       [] => NONE
     | (k, (us, xs)) :: stk' =>
         (case plug (k, (us, xs) \ foc) of
             SOME foc' => SOME (DOWN, foc', stk')
           | NONE => SOME (UNLOAD, foc, stk))

  fun unload (foc, stk) =
    case stk of
       [] => NONE
     | (k, _) :: stk' =>
         let
           val t <: env = foc
           val th `$ args = mapApp (fn HOLE => t | % cl => Cl.force cl) k
           val foc' = th $$ args <: env
         in
           SOME (UNLOAD, foc', stk')
         end

  fun next (mode, foc, stk) =
    case mode of
       DOWN => SOME (down (foc, stk))
     | UP => up (foc, stk)
     | UNLOAD => unload (foc, stk)
end


