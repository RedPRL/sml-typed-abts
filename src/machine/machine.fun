functor AbtMachine (B : ABT_MACHINE_BASIS) : ABT_MACHINE =
struct
  open B B.S B.S.Cl B.S.Cl.Abt

  infix <: \ `$ $ $# $$

  fun getFirstMatch f =
    fn [] => raise Fail "No match"
     | x :: xs => (case f x of SOME y => y | _ => getFirstMatch f xs)

  fun getHoleBinder (_ `$ args) =
    getFirstMatch (fn bs \ HOLE => SOME bs | _ => NONE) args

  fun mapPlus f =
    fn HOLE => HOLE
     | % m => % (f m)

  fun close env m =
    m <: env

  fun makeFrame env (k as th `$ args) =
    let
      fun rho a =
        case Sym.Ctx.find (#params env) a of
           SOME p => p
         | NONE => O.P.pure a
      val th' = O.map rho th
      val args' = List.map (mapBind (mapPlus (close env))) args
    in
      (th' `$ args')
    end

  fun expandFocusedApp (t <: env) =
    case out t of
       th $ args => SOME (th `$ args <: env)
     | _ => NONE

  fun collapseFocusedApp (th `$ args <: env) =
    th $$ args <: env

  fun down sign (foc as t <: env, stk) =
    case out t of
       `x =>
         (case Var.Ctx.find (#terms env) x of
             SOME foc' => (DOWN, foc', stk)
           | NONE => (UNLOAD, foc, stk))
     | _ $# _ => (UNLOAD, foc, stk)
     | th $ args =>
         (case step sign (th `$ args <: env) of
             STEP foc' => (DOWN, foc', stk)
           | THROW foc' => (HANDLE, foc', stk)
           | VAL => (UP, foc, stk)
           | CUT ((k, t) <: env) => (DOWN, t <: env, makeFrame env k :: stk))

  fun up sign (foc : abt app_closure, stk) =
    case stk of
       [] => NONE
     | k :: stk' =>
         let
           val (us, xs) = getHoleBinder k
           val foc' = cut sign (k, (us, xs) \ foc)
         in
           SOME (DOWN, foc', stk')
         end
         handle InvalidCut => SOME (UNLOAD, collapseFocusedApp foc, stk)

  fun handle' sign (foc, stk) =
    case stk of
       [] => NONE
     | k :: stk' =>
         (case getHoleBinder k of
             ([],[]) =>
               (SOME (DOWN, cut sign (k, ([],[]) \ foc), stk')
                  handle InvalidCut => SOME (HANDLE, collapseFocusedApp foc, stk'))
           | _ => SOME (HANDLE, collapseFocusedApp foc, stk'))

  fun unload (foc, stk) =
    case stk of
       [] => NONE
     | k :: stk' =>
         let
           val t <: env = foc
           val th `$ args = mapApp (fn HOLE => t | % cl => Cl.force cl) k
           val foc' = th $$ args <: env
         in
           SOME (UNLOAD, foc', stk')
         end

  fun next sign (mode, foc, stk) =
    case mode of
       DOWN => SOME (down sign (foc, stk))
     | UNLOAD => unload (foc, stk)
     | UP => (case expandFocusedApp foc of SOME foc' => up sign (foc', stk) | _ => SOME (UNLOAD, foc, stk))
     | HANDLE => (case expandFocusedApp foc of SOME foc' => handle' sign (foc', stk) | _ => SOME (UNLOAD, foc, stk))
end

functor AbtMachineUtil (M : ABT_MACHINE) : ABT_MACHINE_UTIL =
struct
  open M M.S M.S.Cl M.S.Cl.Abt

  infix <: `$

  val emptyEnv =
    {params = Sym.Ctx.empty,
     terms = Var.Ctx.empty}

  fun load t =
    (DOWN, t <: emptyEnv, [])

  fun star sign st =
    case next sign st of
       NONE => st
     | SOME st' => star sign st'

  fun unload sign (_, foc, stk) =
    let
      val (_, foc', stk) = star sign (UNLOAD, foc, stk)
    in
      case stk of
         [] => Cl.force foc'
       | _ => raise Fail "AbtMachineUtil.unload: implementation error"
    end

  fun eval sign = unload sign o star sign o load
end
