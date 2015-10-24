signature ABT =
sig
  structure Symbol : SYMBOL
  structure Variable : SYMBOL
  structure Operator : OPERATOR
  structure Metavariable : SYMBOL
  structure Metacontext : METACONTEXT
    where type metavariable = Metavariable.t
    where type valence = Operator.Arity.Valence.t

  type symbol = Symbol.t
  type variable = Variable.t
  type metavariable = Metavariable.t
  type operator = symbol Operator.t
  type sort = Operator.Arity.Sort.t
  type valence = Operator.Arity.Valence.t
  type metacontext = Metacontext.t
  type 'a spine = 'a Operator.Arity.Valence.Spine.t

  type abt
  structure Eq : EQ where type t = abt

  val freeVariables : abt -> variable list
  val freeSymbols : abt -> symbol list

  (* subst (N, x) M ==== [N/x]M *)
  val subst : abt * variable -> abt -> abt

  (* rename (v, u) M === {v/u}M *)
  val rename : symbol * symbol -> abt -> abt

  (* Patterns for abstract binding trees. *)
  datatype 'a view =
      ` of variable
    | $ of operator * 'a spine
    | $# of metavariable * (symbol spine * 'a spine)
    | \ of (symbol spine * variable spine) * 'a

  structure ViewFunctor : FUNCTOR where type 'a t = 'a view

  (* Construct an abt from a view by checking it against a valence. *)
  val check : metacontext -> abt view * valence -> abt

  (* Pattern match on an abt and its valence. *)
  val infer : metacontext -> abt -> valence * abt view
end
