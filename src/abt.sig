signature ABT =
sig
  structure Symbol : SYMBOL
  structure Variable : SYMBOL
  structure Operator : OPERATOR
  structure Metavariable : PRESYMBOL
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
  type btm

  structure Eq : EQ where type t = abt

  val freeVariables : abt -> (variable * sort) list
  val freeSymbols : abt -> (symbol * sort) list
  val metacontext : abt -> metacontext

  (* subst (N, x) M === [N/x]M *)
  val subst : abt * variable -> abt -> abt

  (* metasubst (E, m) M === [E/m]M *)
  val metasubst : btm * metavariable -> abt -> abt

  (* rename (v, u) M === {v/u}M *)
  val rename : symbol * symbol -> abt -> abt

  (* Patterns for abstract binding trees. *)
  datatype 'a bview =
     \ of (symbol spine * variable spine) * 'a
  datatype 'a view =
      ` of variable
    | $ of operator * 'a bview spine
    | $# of metavariable * (symbol spine * 'a spine)

  structure Functor : FUNCTOR
    where type 'a t = 'a view
  structure BFunctor : FUNCTOR
    where type 'a t = 'a bview

  (* construct an abt from a view by checking it against a sort *)
  val check : metacontext -> abt view * sort -> abt

  (* pattern match on an abt and its sort *)
  val infer : abt -> abt view * sort

  (* construct a bound term from a view by checking it against a valence *)
  val checkb : metacontext -> abt bview * valence -> btm

  (* pattern match on a bound term and its valence *)
  val inferb : btm -> abt bview * valence

end
