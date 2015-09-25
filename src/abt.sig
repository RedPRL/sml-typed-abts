signature SORT =
sig
  type sort
  include
    sig
      include EQ
      include SHOW
    end
    where type t = sort
end

signature VALENCE =
sig
  type sort
  type valence = sort list * sort

  include
    sig
      include SHOW
      include EQ
    end
    where type t = valence
end

signature ARITY =
sig
  structure Sort : SORT
  structure Valence : VALENCE
  sharing type Valence.sort = Sort.sort

  type arity = Valence.t list * Sort.t

  include
    sig
      include SHOW
      include EQ
    end
    where type t  = arity
end

(* An arity-indexed family of operators *)
signature OPERATOR =
sig
  structure Arity : ARITY

  type operator
  include
    sig
      include EQ
      include SHOW
    end
    where type t = operator

  val arity : operator -> Arity.arity
end

signature ABT =
sig
  structure Variable : VARIABLE
  structure Operator : OPERATOR

  type variable = Variable.t
  type operator = Operator.t
  type sort = Operator.Arity.Sort.t
  type 'a spine = 'a list

  type abt
  include EQ where type t = abt

  datatype 'a view =
      ` of variable
    | $ of operator * 'a spine
    | \ of variable * 'a

  structure ViewFunctor : FUNCTOR where type 'a t = 'a view
  val check : abt view * Operator.Arity.Valence.t -> abt
  val infer : abt -> Operator.Arity.Valence.t * abt view
end

signature ABT_UTIL =
sig
  include ABT

  datatype star = STAR of star view | EMB of abt
  val checkStar : star * Operator.Arity.Valence.t -> abt
end

