(* This is the main point of interaction with this library. The ABT
 * signature describes every operation generally needed to manipulate syntax.
 *)

signature ABT =
sig
  structure Var : ABT_SYMBOL

  (* Symbols are not variables; they parameterize operators and do not appear as
   * terms in the syntax of abstract binding trees. Therefore, they are subject
   * to apartness-preserving (injective) renamings, and not substitution. *)
  structure Sym : ABT_SYMBOL

  (* Just as variables can be used to stand in for an abt, metavariables can be
   * used to stand in for an abstraction/binder of any valence. Metavars
   * are also sometimes called "second-order variables". *)
  structure Metavar : ABT_SYMBOL

  (* Operators are the primitive building blocks of a language; the [Operator]
   * allows the ABT framework to be deployed at an arbitrary signature of
   * operators. In older texts on universal algebra, sometimes operators are
   * often referred to as "function symbols". *)
  structure O : ABT_OPERATOR

  (* User-supplied type of term annotations; irrelevant as far as equality is concerned.
   * This can be used to add source positions to an abt. *)
  type annotation

  (* Convienent shorthands for the types found in the above structures *)
  type symbol = Sym.t
  type variable = Var.t
  type metavariable = Metavar.t
  type operator = symbol O.t
  type sort = O.Ar.sort
  type psort = O.Ar.psort
  type valence = O.Ar.valence
  type param = symbol O.P.term

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

  (* Patterns for abstract binding trees. *)
  include ABT_VIEWS where type 'a spine = 'a O.Ar.Vl.Sp.t
  type 'a view = (param, psort, symbol, variable, metavariable, operator, 'a) termf
  type 'a bview = (symbol, variable, 'a) bindf
  type 'a appview = (symbol, variable, operator, 'a) appf

  type metactx = valence Metavar.ctx
  type varctx = sort Var.ctx
  type symctx = psort Sym.ctx

  type metaenv = abs Metavar.ctx
  type varenv = abt Var.ctx
  type symenv = param Sym.ctx

  (* Modify the term inside an abstraction*)
  val mapAbs : (abt -> abt) -> abs -> abs

  (* Surround a term with a nullary abstraction *)
  val abtToAbs : abt -> abs

  (* apply a transformation to each immediate subterm *)
  val mapSubterms : (abt -> abt) -> abt -> abt

  (* apply a transformation to all subterms recursively *)
  val deepMapSubterms : (abt -> abt) -> abt -> abt

  (* Decide alpha equivalence of two terms *)
  val eq : abt * abt -> bool
  val eqAbs : abs * abs -> bool

  (* Calculating free metavariables, free variables and free symbols *)
  val metactx : abt -> metactx
  val varctx : abt -> varctx
  val symctx : abt -> symctx

  (* Finding occurrences (ie, annotations) of free variables, symbols,
   * and metavariables. Note that if a variable, symbol, or metavariable
   * is unannotated, it will *not* be included in the result. Thus, these
   * functions are not substitutes to the *ctx functions above, but should
   * only be used in a best-effort attempt to produce useful annotation
   * information on an element of the corresponding *ctx.
   *)
  val varOccurrences : abt -> annotation list Var.ctx
  val symOccurrences : abt -> annotation list Sym.ctx

  val unbind : abs -> symbol spine -> abt spine -> abt
  val // : abs * (symbol spine * abt spine) -> abt

  (* Substitution of metavariables instantiates the bound variables and
   * symbols of the abstraction with the operands of applications of
   * the metavariable. This operation is related to Kevin Watkins' method
   * of hereditary substitution as invented for the Concurrent Logical Framework.
   *)
  val substMetaenv : metaenv -> abt -> abt
  val substVarenv : varenv -> abt -> abt
  val substSymenv : symenv -> abt -> abt

  exception BadSubstMetaenv of {metaenv : metaenv, term : abt, description : string}

  (* Below we provide unary versions of the simultaneous substitution operations *)
  val substMetavar : abs * metavariable -> abt -> abt
  val substVar : abt * variable -> abt -> abt
  val substSymbol : param * symbol -> abt -> abt

  val annotate : annotation -> abt -> abt
  val getAnnotation : abt -> annotation option
  val setAnnotation : annotation option -> abt -> abt
  val clearAnnotation : abt -> abt

  (* Note: The [check] operation corresponds to the [into] operation found in
   * the Carnegie Mellon ABT libraries.
   *)

  (* construct an abt from a view by checking it against a sort. *)
  val check : abt view * sort -> abt

  val $$ : operator * abt bview spine -> abt

  (* pattern match on an abt and its sort *)
  val infer : abt -> abt view * sort
  val out : abt -> abt view
  val sort : abt -> sort

  (* construct an abstraction from a view by checking it against a valence *)
  val checkb : abt bview * valence -> abs

  (* pattern match on an abstraction and its valence *)
  val inferb : abs -> abt bview * valence
  val outb : abs -> abt bview
  val valence : abs -> valence

  val primToString : abt -> string 
  val primToStringAbs : abs -> string 

  (* alpha unification *)
  structure Unify :
  sig
    type renaming = metavariable Metavar.ctx * symbol Sym.ctx * variable Var.ctx

    (* unify by synthesizing a renaming of metavariables and variables; raises
    * [UnificationFailed] when no renaming can be synthesized. *)
    val unify : abt * abt -> renaming
    exception UnificationFailed

    val unifyOpt :  abt * abt -> renaming option
  end

  val primToString : abt -> string
  val primToStringAbs : abs -> string
end
