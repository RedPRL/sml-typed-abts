signature PATTERN =
sig
  type operator
  type metavariable
  type metacontext
  type 'a spine

  (* A pattern is a description of a set of ABTs. It describes the
   * overall shape but may leave some pieces out. Specifically, instead
   * of an ABT which is
   *  - An operator applied to other abstractions
   *  - A variable
   *  - A metavariable
   * a pattern is
   *  - An operator applied to patterns (no abstractions!)
   *  - A metavariable
   * The metavariables are slightly different though, they cannot be applied
   * and they're used to stand for some "normal" abt, not a pattern. Patterns
   * must be linear; each metavariable may occur only once.
   *)
  type pattern

  datatype 'a argument =
      MVAR of metavariable
    | PAT of 'a

  (* When [pat] is a pattern with metacontext [Θ] and [m] is a closed term in
   * metacontext [Θ], then [p ~> m] is a rewrite rule. *)
  datatype 'a view = $@ of operator * 'a argument spine

  structure Error :
  sig
    datatype t =
        NON_LINEAR
      | OTHER
  end

  exception InvalidPattern of Error.t

  (* Construct a valid linear abt pattern *)
  val into : pattern view -> pattern

  (* Inspect a linear abt pattern and its metavariable context *)
  val out : pattern -> pattern view * metacontext
end

signature LIST_ABT =
  ABT where type 'a Operator.Arity.Valence.Spine.t = 'a list

(* ABT_PATTERN is just the pairing of an implementation of
 * normal abts with an implementation of patterns on them
 *)
signature ABT_PATTERN =
sig
  structure Abt : LIST_ABT
  structure Pattern : PATTERN
    where type operator = Abt.operator
    where type metavariable = Abt.metavariable
    where type metacontext = Abt.metacontext
    where type 'a spine = 'a Abt.spine
end
