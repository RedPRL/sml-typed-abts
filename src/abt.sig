(* This is the main point of interaction with this library. The ABT
 * signature describes every operation generally needed to manipulate syntax.
 *)

signature ABT =
sig
  (* An ABT implementation is built upon several smaller concepts any of which
   * may be tweaked. The [Variable] and [Symbol] structures controls what
   * implementation of nominal atoms we use for variables/symbols respectively.
   * [Operator] control what the primitive operators are as well as determines
   * their arities.
   *)
  structure Variable : SYMBOL
  structure Operator : OPERATOR

  structure Symbol : SYMBOL

  (* In addition to all of the above, it is very useful to consider ABTs
   * with chunks of the actual syntax being left out. This may come up for
   * example when to model terms which are unified. In order to do this properly,
   * a new level of variable is introduced which ranges over abstractions rather
   * than terms.
   *)
  structure Metavariable : PRESYMBOL
  structure Metacontext : METACONTEXT
    where type metavariable = Metavariable.t
    where type valence = Operator.Arity.Valence.t

  (* Convienent shorthands for the types found in the above structures *)
  type symbol = Symbol.t
  type variable = Variable.t
  type metavariable = Metavariable.t
  type operator = symbol Operator.t
  type sort = Operator.Arity.Sort.t
  type valence = Operator.Arity.Valence.t
  type metacontext = Metacontext.t
  type 'a spine = 'a Operator.Arity.Valence.Spine.t

  (* The core type of the signature. This is the type of the ABTs that
   * can be built from the given [operator]s, [variable]s, [symbol]s and
   * [metavariable]s
   *)
  type abt

  (* An abs is an *abs*straction. It's the portion of syntax which binds
   * variables and symbols for use in a term. It's conceptually separate
   * from the abt type because it doesn't make sense to have a binder outside
   * the context of some operator.
   *)
  type abs

  (* Equality on ABTs is the "right" sort of equality even though it's
   * a little complicated. It considers terms up to
   *  1. Alpha-varying bound variables
   *  2. Apartness preserving renamings of bound symbols
   *)
  structure Eq : EQ where type t = abt

  val freeVariables : abt -> (variable * sort) list
  val freeSymbols : abt -> (symbol * sort) list

  (* This should be thought of as a "freeVariables" like function but
   * in addition to just returning what metavariables are in scope,
   * it also gives back information on the valence of each operator
   * in a format that supports efficient random access
   *)
  val metacontext : abt -> metacontext

  (* subst (N, x) M === [N/x]M *)
  val subst : abt * variable -> abt -> abt

  (* metasubst (E, m) M === [E/m]M.
   * Note that substitution of metavariables automatically
   * instantiates the bound variables and symbols of the abstraction E
   * with the operands of applications of the metavariable m. This
   * operation is derived from Kevin Watkins' method of hereditary
   * substitution as invented for the Concurrent Logical Framework.
   *)
  val metasubst : abs * metavariable -> abt -> abt

  (* rename (v, u) M === {v/u}M *)
  val rename : symbol * symbol -> abt -> abt

  (* Patterns for abstract binding trees. *)

  (* A bview is a view of a abstraction. This is NOT an abt;
   * a binding is a spine of symbols
   * and variables as well as the underlying 'a (usually an abt)
   * that uses them. Note that unlike previous ABT libraries, this avoids
   * the annoying issue of unpacking an operator and getting back
   * an "abt" that really makes no sense with the operator.
   *)
  datatype 'a bview =
     \ of (symbol spine * variable spine) * 'a

  (* This is the main interface to be used for interacting with
   * an ABT. When inspected, an standard ABT is just a variable or
   * an operator (the binding case is always wrapped in an operators
   * argument) or a metavariable applied to some collection of
   * symbols and terms
   *)
  datatype 'a view =
      ` of variable
    | $ of operator * 'a bview spine
    | $# of metavariable * (symbol spine * 'a spine)

  structure Functor : FUNCTOR
    where type 'a t = 'a view
  structure BFunctor : FUNCTOR
    where type 'a t = 'a bview

  (* Note that if you're used to CMU's abt library,
   *  - into ===> check
   *  - out  ===> infer
   *)

  (* construct an abt from a view by checking it against a sort. *)
  val check : metacontext -> abt view * sort -> abt

  (* pattern match on an abt and its sort *)
  val infer : abt -> abt view * sort

  (* construct an abstraction from a view by checking it against a valence *)
  val checkb : metacontext -> abt bview * valence -> abs

  (* pattern match on an abstraction and its valence *)
  val inferb : abs -> abt bview * valence

end
