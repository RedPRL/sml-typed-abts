(* This is the main point of interaction with this library. The ABT
 * signature describes every operation generally needed to manipulate syntax.
 *)

signature ABT =
sig
  structure Variable : SYMBOL

  (* Symbols are not variables; they parameterize operators and do not appear as
   * terms in the syntax of abstract binding trees. Therefore, they are subject
   * to apartness-preserving (injective) renamings, and not substitution. *)
  structure Symbol : SYMBOL

  (* Just as variables can be used to stand in for an abt, metavariables can be
   * used to stand in for an abstraction/binder of any valence. Metavariables
   * are also sometimes called "second-order variables". *)
  structure Metavariable : PRESYMBOL

  (* Operators are the primitive building blocks of a language; the [Operator]
   * allows the ABT framework to be deployed at an arbitrary signature of
   * operators. In older texts on universal algebra, sometimes operators are
   * often referred to as "function symbols". *)
  structure Operator : OPERATOR

  (* Convienent shorthands for the types found in the above structures *)
  type symbol = Symbol.t
  type variable = Variable.t
  type metavariable = Metavariable.t
  type operator = symbol Operator.t
  type sort = Operator.Arity.Valence.sort
  type valence = Operator.Arity.valence
  type 'a spine = 'a Operator.Arity.Valence.Spine.t

  structure MetaCtx : DICT where type key = metavariable
  structure VarCtx : DICT where type key = variable
  structure SymCtx : DICT where type key = symbol

  (* The core type of the signature. This is the type of the ABTs that
   * can be built from the given [operator]s, [variable]s, [symbol]s and
   * [metavariable]s
   *)
  type abt

  (* An abs is an *abs*straction. It's the portion of syntax which binds
   * variables and symbols for use in a term. It's conceptually separate
   * from the abt type because abstractions only occur as the arguments to
   * an operator.
   *)
  type abs

  type metactx = valence MetaCtx.dict
  type varctx = sort VarCtx.dict
  type symctx = sort SymCtx.dict

  type metaenv = abs MetaCtx.dict
  type varenv = abt VarCtx.dict
  type symenv = symbol SymCtx.dict

  (* Modify the term inside an abstraction*)
  val mapAbs : (abt -> abt) -> abs -> abs

  (* Decide alpha equivalence of two terms *)
  val eq : abt * abt -> bool

  (* Calculating free metavariables, free variables and free symbols *)
  val metactx : abt -> metactx
  val varctx : abt -> varctx
  val symctx : abt -> symctx

  (* Substitution of metavariables instantiates the bound variables and
   * symbols of the abstraction with the operands of applications of
   * the metavariable. This operation is related to Kevin Watkins' method
   * of hereditary substitution as invented for the Concurrent Logical Framework.
   *)
  val metasubstEnv : metaenv -> abt -> abt
  val substEnv : varenv -> abt -> abt

  (* Below we provide unary versions of the simultaneous substitution operations *)
  val metasubst : abs * metavariable -> abt -> abt
  val subst : abt * variable -> abt -> abt
  val rename : symbol * symbol -> abt -> abt

  (* Patterns for abstract binding trees. *)

  (* A bview is a view of a abstraction. This is NOT an abt;
   * a binding is a spine of symbols and variables as well as the
   * underlying 'a (usually an abt) that uses them.
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

  val map : ('a -> 'b) -> 'a view -> 'b view
  val mapb : ('a -> 'b) -> 'a bview -> 'b bview

  structure BFunctor : FUNCTOR
    where type 'a t = 'a bview

  (* The [check] operation corresponds to the [into] operation found in the
   * Carnegie Mellon ABT libraries.
   *)

  (* construct an abt from a view by checking it against a sort. *)
  val check : metactx -> abt view * sort -> abt
  val check' : abt view * sort -> abt

  (* pattern match on an abt and its sort *)
  val infer : abt -> abt view * sort
  val out : abt -> abt view
  val sort : abt -> sort

  (* construct an abstraction from a view by checking it against a valence *)
  val checkb : metactx -> abt bview * valence -> abs
  val checkb' : abt bview * valence -> abs

  (* pattern match on an abstraction and its valence *)
  val inferb : abs -> abt bview * valence
  val outb : abs -> abt bview
  val valence : abs -> valence

end
