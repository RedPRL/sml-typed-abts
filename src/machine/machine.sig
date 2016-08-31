(* The minimal basis for generating an abstract machine for an ABT signature. *)
signature ABT_MACHINE_BASIS =
sig
  structure S : ABT_MACHINE_STATE where type 'a Cl.Abt.O.Ar.Vl.Sp.t = 'a list

  (* How shall a focused term compute? See the documentation for M.step. *)
  val step : S.abt S.app_closure -> S.abt S.step

  exception InvalidCut

  (* How to cut a canonical form into a stack frame. For instance "cut (fst, (m,n)) ~> m".
     This procedure is also used for handling exceptions.  Raises InvalidCut. *)
  val cut : S.abt S.frame * S.abt S.app_closure S.binding -> S.abt S.closure
end

signature ABT_MACHINE =
sig
  include ABT_MACHINE_BASIS

  val next : S.abt S.state -> S.abt S.state option
end

signature ABT_MACHINE_UTIL =
sig
  include ABT_MACHINE

  val load : S.abt -> S.abt S.state
  val unload : S.abt S.state -> S.abt

  (* reflexive-transitive closure of the transition relation *)
  val star : S.abt S.state -> S.abt S.state

  val eval : S.abt -> S.abt
end
