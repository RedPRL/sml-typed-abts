signature COORD =
sig
  type t
  val origin : t
  val shiftRight : t -> t
  val shiftDown : t -> t
  include EQ
end

structure Coord :> COORD =
struct
  type t = int * int
  val origin = (0,0)
  fun shiftRight (i, j) = (i, j + 1)
  fun shiftDown (i, j) = (i + 1, j)
  fun eq (x : t, y : t) = x = y
end


functor Abt (structure Variable : VARIABLE and Operator : OPERATOR) : ABT =
struct

  structure Variable = Variable and Operator = Operator and Arity = Operator.Arity

  type variable = Variable.t
  type operator = Operator.t
  type sort = Arity.Sort.t
  type valence = Arity.Valence.t

  structure Spine = Arity.Spine
  type 'a spine = 'a Spine.t

  datatype abt =
      FV of variable * sort
    | BV of Coord.t * sort
    | ABS of (variable * sort) list * abt
    | APP of operator * abt spine

  datatype 'a view =
      ` of variable
    | $ of operator * 'a spine
    | \ of variable list * 'a

  infixr 5 \
  infix 5 $

  structure ViewFunctor =
  struct
    type 'a t = 'a view
    fun map f e =
      case e of
          ` x => ` x
       | x \ e => x \ f e
       | theta $ es => theta $ Spine.Functor.map f es
  end

  (* TODO: replace with efficient check! *)
  fun disjoint [] = true
    | disjoint (v::vs) =
        disjoint vs andalso List.all (fn v' => not (Variable.eq (v, v'))) vs

  fun shiftVariable v coord e =
    case e of
         FV (v', sigma) => if Variable.eq (v, v') then BV (coord, sigma) else e
       | BV _ => e
       | ABS (xs, e') => ABS (xs, shiftVariable v (Coord.shiftRight coord) e')
       | APP (theta, es) => APP (theta, Spine.Functor.map (shiftVariable v coord) es)

  fun addVariable v coord e =
    case e of
         FV _ => e
       | BV (ann as (coord', sigma)) =>
           if Coord.eq (coord, coord') then FV (v, sigma) else BV ann
       | ABS (xs, e) => ABS (xs, addVariable v (Coord.shiftRight coord) e)
       | APP (theta, es) => APP (theta, Spine.Functor.map (addVariable v coord) es)

  fun traverseVariables f vs =
    let
      val true = disjoint vs
      fun go [] coord e = e
        | go (v::vs) coord e =
            go vs (Coord.shiftDown coord) (f v coord e)
    in
      go vs
    end

  val shiftVariables = traverseVariables shiftVariable
  val addVariables = traverseVariables addVariable

  fun check (`x, ([], sigma)) = FV (x, sigma)
    | check (xs \ e, (sorts, tau)) =
      let
        val ((_, tau'), _) = infer e
        val true = Arity.Sort.eq (tau, tau')
      in
        ABS (ListPair.zipEq (xs, sorts), shiftVariables xs Coord.origin e)
      end
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

        val es' = Spine.Pair.mapEq chkInf (valences, es)
      in
        APP (theta, es')
      end
    | check (_, (sorts, _)) = raise Match

  and infer (FV (v, sigma)) = (([], sigma), ` v)
    | infer (BV _) = raise Fail "Impossible: unexpected bound variable"
    | infer (ABS (xs, e)) =
      let
        val xs' = List.map (Variable.clone o #1) xs
        val (([], tau), e') = infer e
        val valence = (List.map #2 xs, tau)
      in
        (valence, xs' \ addVariables xs' Coord.origin e)
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
      | eq (BV (i, _), BV (j, _)) = Coord.eq (i, j)
      | eq (ABS (_, e), ABS (_, e')) = eq (e, e')
      | eq (APP (theta, es), APP (theta', es')) =
          Operator.eq (theta, theta') andalso Spine.Pair.allEq eq (es, es')
      | eq _ = false
  end

  open Eq
end
