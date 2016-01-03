signature PATTERN =
sig
  type operator
  type metavariable
  type metacontext
  type 'a spine

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

signature ABT_PATTERN =
sig
  structure Abt : LIST_ABT
  structure Pattern : PATTERN
    where type operator = Abt.operator
    where type metavariable = Abt.metavariable
    where type metacontext = Abt.metacontext
    where type 'a spine = 'a Abt.spine
end
