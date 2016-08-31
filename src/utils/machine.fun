functor AbtMachineState (Cl : ABT_CLOSURE) : ABT_MACHINE_STATE =
struct
  structure Cl = Cl

  type abt = Cl.Abt.abt
  type 'a binding = 'a Cl.Abt.bview

  datatype 'a plus = HOLE | % of 'a

  type 'a closure = ('a, 'a) Cl.closure

  (* An application of the "signature endofunctor", i.e. a term headed by an operator *)
  type 'a application = 'a Cl.Abt.appview
  type 'a app_closure = ('a application, 'a) Cl.closure

  (* a continuation is an application with a single hole in it *)
  type 'a continuation = 'a plus application

  (* a stack frame is a continuation whose subterms are closures *)
  type 'a frame = 'a closure continuation
  type 'a stack = 'a frame list

  (* there are four modes to our machine state:
       1. DOWN means we are computing the focused term to a canonical form
       2. UP means we are passing the focused term to the first stack frame
       3. HANDLE means we are passing the focused exception up the stack until it hits a suitable handler
       4. UNLOAD means that our focused term is neutral, so we are unwinding the stack
   *)
  datatype mode =
     DOWN
   | UP
   | HANDLE
   | UNLOAD

  (* A machine state consists in a mode, a focused term/closure, and a control stack. *)
  type 'a state = mode * 'a closure * 'a stack

  (* This "view" tells us a bit about how the focused term should be computed.
       1. STEP means that the focused term can step to another term, requiring no input from the stack
       2. THROW means that the focused term is throwing an exception
       3. CUT means that the focused term can only be computed on the basis of the canonical form of its input
       4. VAL means that the focused term is a canonical form
   *)
  datatype 'a step =
     STEP of 'a closure
   | THROW of 'a closure
   | CUT of ('a plus application * 'a, 'a) Cl.closure
   | VAL
end


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
           | THROW foc' => (HANDLE, foc', stk)
           | VAL => (UP, foc, stk)
           | CUT ((k, t) <: env) => (DOWN, t <: env, makeFrame env k :: stk))

  fun up (foc : abt app_closure, stk) =
    case stk of
       [] => NONE
     | k :: stk' =>
         let
           val (us, xs) = getHoleBinder k
           val foc' = cut (k, (us, xs) \ foc)
         in
           SOME (DOWN, foc', stk')
         end
         handle InvalidCut => SOME (UNLOAD, collapseFocusedApp foc, stk)

  fun handle' (foc, stk) =
    case stk of
       [] => NONE
     | k :: stk' =>
         let
           val ([], []) = getHoleBinder k
           val foc' = cut (k, ([], []) \ foc)
         in
           SOME (DOWN, foc', stk')
         end
         handle InvalidCut => SOME (HANDLE, collapseFocusedApp foc, stk)

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

  fun next (mode, foc, stk) =
    case mode of
       DOWN => SOME (down (foc, stk))
     | UNLOAD => unload (foc, stk)
     | UP => (case expandFocusedApp foc of SOME foc' => up (foc', stk) | _ => SOME (UNLOAD, foc, stk))
     | HANDLE => (case expandFocusedApp foc of SOME foc' => handle' (foc', stk) | _ => SOME (UNLOAD, foc, stk))
end
