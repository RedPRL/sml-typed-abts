functor Abt
  (structure Symbol : SYMBOL
   structure Variable : SYMBOL
   structure Operator : OPERATOR) : ABT =
struct

  structure Symbol = Symbol and Variable = Variable and Operator = Operator and Arity = Operator.Arity
  structure Sort = Arity.Sort and Valence = Arity.Valence
  structure Spine = Valence.Spine

  type symbol = Symbol.t
  type variable = Variable.t
  type operator = symbol Operator.t
  type sort = Sort.t
  type valence = Valence.t
  type coord = Coord.t

  type 'a spine = 'a Spine.t

  structure LN =
  struct
    datatype 'a t =
        FREE of 'a
      | BOUND of coord

    functor Eq (I : EQ) : EQ =
    struct
      type t = I.t t
      fun eq (FREE v, FREE v') = I.eq (v, v')
        | eq (BOUND i, BOUND j) = Coord.Eq.eq (i, j)
        | eq _ = false
    end

    type symbol = symbol t
    type operator = symbol Operator.t
    type variable = variable t

    exception UnexpectedBoundName of coord
    fun getFree (FREE v) = v
      | getFree (BOUND i) = raise UnexpectedBoundName i
  end

  datatype abt =
      V of LN.variable * sort
    | ABS of (variable * sort) spine * abt
    | APP of LN.operator * abt spine

  datatype 'a view =
      ` of variable
    | $ of operator * 'a spine
    | \ of variable spine * 'a

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


  fun imprisonVariable v (coord, e) =
    case e of
         V (LN.FREE v', sigma) =>
           if Variable.Eq.eq (v, v') then V (LN.BOUND coord, sigma) else e
       | V _ => e
       | ABS (xs, e') => ABS (xs, imprisonVariable v (Coord.shiftRight coord, e'))
       | APP (theta, es) =>
           APP (theta, Spine.Functor.map (fn e => imprisonVariable v (coord, e)) es)

  fun liberateVariable v (coord, e) =
    case e of
         V (LN.FREE _, _) => e
       | ann as V (LN.BOUND coord', sigma) =>
           if Coord.Eq.eq (coord, coord') then V (LN.FREE v, sigma) else ann
       | ABS (xs, e) => ABS (xs, liberateVariable v (Coord.shiftRight coord, e))
       | APP (theta, es) =>
           APP (theta, Spine.Functor.map (fn e => liberateVariable v (coord, e)) es)

  local
    structure ShiftFunCat : CATEGORY =
    struct
      type ('a, 'b) hom = (coord * 'a -> 'b)
      fun id (_, x) = x
      fun comp (f, g) (coord, a) = f (coord, g (Coord.shiftDown coord, a))
    end

    structure ShiftFoldMap =
      CategoryFoldMap
        (structure C = ShiftFunCat
         structure F = Spine.Foldable)
  in
    fun imprisonVariables vs t =
      ShiftFoldMap.foldMap imprisonVariable vs (Coord.origin, t)

    fun liberateVariables vs t =
      ShiftFoldMap.foldMap liberateVariable vs (Coord.origin, t)
  end

  fun assert msg b =
    if b then () else raise Fail msg

  fun assertSortEq (sigma, tau) =
    assert
      ("expected " ^ Sort.Show.toString sigma ^ " == " ^ Sort.Show.toString tau)
      (Sort.Eq.eq (sigma, tau))

  fun assertValenceEq (v1, v2) =
    assert
      ("expected " ^ Valence.Show.toString v1 ^ " == " ^ Valence.Show.toString v2)
      (Valence.Eq.eq (v1, v2))

  fun check (e, valence as (sorts, sigma)) =
    case e of
         `x =>
           let
             val () = assert "sorts not empty" (Spine.isEmpty sorts)
           in
             V (LN.FREE x, sigma)
           end
       | xs \ e =>
           let
             val ((_, tau), _) = infer e
             val () = assertSortEq (sigma, tau)
           in
             ABS (Spine.Pair.zipEq (xs, sorts), imprisonVariables xs e)
           end
       | theta $ es =>
           let
             val () = assert "sorts not empty" (Spine.isEmpty sorts)
             val (_, (valences, tau)) = Operator.proj theta
             val () = assertSortEq (sigma, tau)
             fun chkInf (e, valence) =
               let
                 val (valence', _) = infer e
                 val () = assertValenceEq (valence, valence')
               in
                 e
               end
             val theta' = Operator.Renaming.map LN.FREE theta
           in
             APP (theta', Spine.Pair.mapEq chkInf (es, valences))
           end

  and infer (V (LN.FREE v, sigma)) = ((Spine.empty (), sigma), ` v)
    | infer (V _) = raise Fail "Impossible: unexpected bound variable"
    | infer (ABS (bindings, e)) =
      let
        val xs = Spine.Functor.map (Variable.clone o #1) bindings
        val (sorts, tau) = inferValence e
        val () = assert "sorts not empty" (Spine.isEmpty sorts)
        val valence = (Spine.Functor.map #2 bindings, tau)
      in
        (valence, xs \ liberateVariables xs e)
      end
    | infer (APP (theta, es)) =
      let
        val (_, (_, tau)) = Operator.proj theta
        val theta' = Operator.Renaming.map LN.getFree theta
      in
        ((Spine.empty (), tau), theta' $ es)
      end

  and inferValence (V (LN.FREE v, sigma)) = (Spine.empty (), sigma)
    | inferValence (V (LN.BOUND i, sigma)) = (Spine.empty (), sigma)
    | inferValence (ABS (bindings, e)) =
      let
        val (_, sigma) = inferValence e
        val sorts = Spine.Functor.map #2 bindings
      in
        (sorts, sigma)
      end
    | inferValence (APP (theta, es)) =
      let
        val (_, (_, sigma)) = Operator.proj theta
      in
        (Spine.empty (), sigma)
      end

  structure Eq : EQ =
  struct
    type t = abt
    structure LnVarEq = LN.Eq (Variable.Eq)
    structure LnSymEq = LN.Eq (Symbol.Eq)
    structure OpLnEq = Operator.Eq (LnSymEq)
    structure OpEq = Operator.Eq (Symbol.Eq)
    fun eq (V (v, _), V (v', _)) = LnVarEq.eq (v, v')
      | eq (ABS (_, e), ABS (_, e')) = eq (e, e')
      | eq (APP (theta, es), APP (theta', es')) =
          OpLnEq.eq (theta, theta') andalso Spine.Pair.allEq eq (es, es')
      | eq _ = false
  end
end
