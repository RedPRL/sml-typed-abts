signature ABT =
sig
  structure Variable : VARIABLE
  structure Operator : OPERATOR

  type variable = Variable.t
  type operator = Operator.t
  type sort = Operator.Arity.Sort.t
  type valence = Operator.Arity.Valence.t
  type 'a spine = 'a Operator.Arity.Spine.t

  type abt
  include EQ where type t = abt

  datatype 'a view =
      ` of variable
    | $ of operator * 'a spine
    | \ of variable list * 'a

  structure ViewFunctor : FUNCTOR where type 'a t = 'a view
  val check : abt view * valence -> abt
  val infer : abt -> valence * abt view
end
