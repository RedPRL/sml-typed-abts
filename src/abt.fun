functor ShowAbt (Abt : ABT) :> SHOW where type t = Abt.abt =
struct
  open Abt infix $ infixr \
  type t = abt

  fun toString e =
    case #2 (infer e) of
         `x => Variable.toString x
       | x \ e => Variable.toString x ^ "." ^ toString e
       | theta $ es =>
           Operator.toString theta ^ "(" ^ ListPretty.pretty toString ("; ", es) ^ ")"
end

functor AbtUtil (Abt : ABT) : ABT_UTIL =
struct
  open Abt

  datatype star = STAR of star view | EMB of abt

  infixr 5 \
  infix 5 $

  fun checkStar (STAR (`x) , valence) = check (`x, valence)
    | checkStar (STAR (x \ ast), valence as (sigma :: sorts, tau)) =
      let
        val e = checkStar (ast, (sorts, tau))
      in
        check (x \ e, valence)
      end
    | checkStar (STAR (theta $ asts), valence) =
      let
        val (valences, _) = Operator.arity theta
        val es = ListPair.mapEq checkStar (asts, valences)
      in
        check (theta $ es, valence)
      end
    | checkStar (EMB e, valence) =
      let
        val (valence', e') = infer e
        val true = Operator.Arity.Valence.eq (valence, valence')
      in
        e
      end
    | checkStar _ = raise Match

end

functor Abt (structure Variable : VARIABLE and Operator : OPERATOR) : ABT =
struct

  structure Variable = Variable and Operator = Operator and Arity = Operator.Arity

  type variable = Variable.t
  type operator = Operator.t
  type sort = Arity.Sort.t
  type valence = Arity.Valence.t
  type 'a spine = 'a list

  datatype abt =
      FV of variable * sort
    | BV of int * sort
    | ABS of variable * sort * abt
    | APP of operator * abt spine

  datatype 'a view =
      ` of variable
    | $ of operator * 'a spine
    | \ of variable * 'a

  infixr 5 \
  infix 5 $

  structure ViewFunctor =
  struct
    type 'a t = 'a view
    fun map f e =
      case e of
          ` x => ` x
       | x \ e => x \ f e
       | theta $ es => theta $ List.map f es
  end

  fun shiftVariable v n e =
    case e of
        FV (v', sigma) =>
        if Variable.eq (v, v') then
          BV (n, sigma)
        else
          FV (v', sigma)
      | BV v => BV v
      | ABS (x, sigma, e') => ABS (x, sigma, shiftVariable v (n + 1) e')
      | APP (theta, es) => APP (theta, List.map (shiftVariable v n) es)

  fun addVariable v n e =
    case e of
        FV v' => FV v'
      | BV (v' as (m, sigma)) =>
        if m = n then FV (v, sigma) else BV v'
      | ABS (x, sigma, e) => ABS (x, sigma, addVariable v (n + 1) e)
      | APP (theta, es) => APP (theta, List.map (addVariable v n) es)

  fun check (` x, ([], sigma)) = FV (x, sigma)
    | check (x \ e, (sigma::sorts, tau)) = ABS (x, sigma, shiftVariable x 0 e)
    | check (theta $ es, ([], tau)) =
      let
        val (valences, tau') = Operator.arity theta
        val true = Arity.Sort.eq (tau, tau')
        fun chkInf (valence : Arity.Valence.t, e) =
          let
            val (valence' : Arity.Valence.t, _) = infer e
          in
            if Arity.Valence.eq (valence, valence') then
              e
            else
              raise Fail "valence mismatch"
          end

        val es' = ListPair.mapEq chkInf (valences, es)
      in
        APP (theta, es')
      end
    | check _ = raise Match

  and infer (FV (v, sigma)) = (([], sigma), ` v)
    | infer (BV i) = raise Fail "Impossible: Unexpected bound variable"
    | infer (ABS (x, sigma, e)) =
      let
        val x' = Variable.clone x
        val ((sorts, tau), e') = infer e
        val valence = (sigma :: sorts, tau)
      in
        (valence, x' \ addVariable x' 0 e)
      end
    | infer (APP (theta, es)) =
      let
        val (_, tau) = Operator.arity theta
      in
        (([], tau), theta $ es)
      end

  structure Eq : EQ =
  struct
    type t = abt
    fun eq (FV (v, _), FV (v', _)) = Variable.eq (v, v')
      | eq (BV (i, _), BV (j, _)) = i = j
      | eq (ABS (_, _, e), ABS (_, _, e')) = eq (e, e')
      | eq (APP (theta, es), APP (theta', es')) =
          Operator.eq (theta, theta') andalso ListPair.allEq eq (es, es')
      | eq _ = false
  end

  open Eq
end
