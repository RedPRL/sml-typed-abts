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

  val freeVariables : abt -> (variable * sort) list
  val freeSymbols : abt -> (symbol * sort) list

  (* subst (N, x) M ==== [N/x]M *)
  val subst : abt * variable -> abt -> abt

  (* rename (v, u) M === {v/u}M *)
  val rename : symbol * symbol -> abt -> abt

  (* Patterns for abstract binding trees. *)
  datatype 'tm view =
      ` of variable
    | $ of operator * 'tm bview spine
    | $# of metavariable * (symbol spine * 'tm spine)
  and 'tm bview =
     \ of (symbol spine * variable spine) * 'tm

  structure BFunctor : FUNCTOR
    where type 'a t = 'a bview

  val check : metacontext -> abt view -> sort -> abt
  val infer : metacontext -> abt -> abt view * sort

     (*
  (* Construct an abt from a view by checking it against a valence. *)
  val check : metacontext -> abt btm * valence -> abt

  (* Pattern match on an abt and its valence. *)
  val infer : metacontext -> abt -> valence * abt view
  *)
end
