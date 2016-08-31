signature ABT_MACHINE_STATE =
sig
  structure Cl : ABT_CLOSURE

  datatype 'a plus = HOLE | % of 'a

  type 'a closure = ('a, 'a) Cl.closure

  (* An application of the "signature endofunctor", i.e. a term headed by an operator *)
  type 'a application = 'a Cl.Abt.appview

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

(* The minimal basis for generating an abstract machine for an ABT signature. *)
signature ABT_MACHINE_BASIS =
sig
  structure M : ABT_MACHINE_STATE where type 'a Cl.Abt.O.Ar.Vl.Sp.t = 'a list
  type abt = M.Cl.Abt.abt

  (* How shall a focused term compute? See the documentation for M.step. *)
  val step : (abt M.application, abt) M.Cl.closure -> abt M.step

  (* How to cut a canonical form into a stack frame. For instance "cut (fst, (m,n)) ~> m".
     This procedure is also used for handling exceptions. *)
  val cut : abt M.frame * abt M.closure M.Cl.Abt.bview -> abt M.closure option
end

signature ABT_MACHINE =
sig
  include ABT_MACHINE_BASIS

  val load : abt -> abt M.state
  val next : abt M.state -> abt M.state option
end
