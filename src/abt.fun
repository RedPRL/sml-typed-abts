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

    structure Functor : FUNCTOR =
    struct
      type 'a t = 'a t
      fun map f (FREE v) = FREE (f v)
        | map f (BOUND i) = BOUND i
    end
  end

  datatype abt =
      V of LN.variable * sort
    | ABS of (symbol * sort) spine * (variable * sort) spine * abt
    | APP of LN.operator * abt spine

  datatype 'a view =
      ` of variable
    | $ of operator * 'a spine
    | \ of (symbol spine * variable spine) * 'a

  infixr 5 \
  infix 5 $

  functor Union (Eq : EQ) =
  struct
    fun elem (X, x) = List.exists (fn y => Eq.eq (x, y)) X
    fun union ([], Y) = Y
      | union (x :: X, Y) = if elem (Y, x) then union (X, Y) else x :: (union (X,  Y))
  end

  local
    structure VS = Union (Symbol.Eq)
    structure VU = Union (Variable.Eq)
  in
    fun freeVariables M =
      let
        fun go R (V (LN.FREE v, _)) = VU.union ([v], R)
          | go R (ABS (_, _, M)) = go R M
          | go R (APP (theta, Es)) =
              Spine.Foldable.foldr VU.union R (Spine.Functor.map (go []) Es)
          | go R _ = R
      in
        go [] M
      end

    fun freeSymbols M =
      let
        fun opFreeSymbols theta =
          let
            val (Ypsilon, _) = Operator.proj theta
          in
            List.foldl (fn ((u, _), R) => LN.getFree u :: R handle _ => R) [] Ypsilon
          end
        fun go R (ABS (_, _, M)) = go R M
          | go R (APP (theta, Es)) =
              VS.union (opFreeSymbols theta, Spine.Foldable.foldr VS.union R (Spine.Functor.map (go []) Es))
          | go R _ = R
      in
        go [] M
      end
  end

  fun subst (N, x) M =
    case M of
         V (LN.FREE y, sigma) => if Variable.Eq.eq (x, y) then N else M
       | V _ => M
       | ABS (_, _, M') => subst (N, x) M'
       | APP (theta, Es) =>
           APP (theta, Spine.Functor.map (subst (N, x)) Es)

  fun rename (v, u) =
    let
      fun go M =
        case M of
             V _ => M
           | ABS (_, _, M') => go M'
           | APP (theta, Es) =>
             let
               fun rho u' = if Symbol.Eq.eq (u, u') then v else u'
               val theta' = Operator.Presheaf.map (LN.Functor.map rho) theta
             in
               APP (theta', Spine.Functor.map go Es)
             end
    in
      fn M =>
        if List.exists (fn v' => Symbol.Eq.eq (v', v)) (freeSymbols M) then
          raise Fail "Renaming fails to preserve apartness"
        else
          go M
    end

  structure ViewFunctor =
  struct
    type 'a t = 'a view
    fun map f e =
      case e of
          ` x => ` x
       | (us, xs) \ e => (us, xs) \ f e
       | theta $ es => theta $ Spine.Functor.map f es
  end

  fun imprisonVariable v (coord, e) =
    case e of
         V (LN.FREE v', sigma) =>
           if Variable.Eq.eq (v, v') then V (LN.BOUND coord, sigma) else e
       | V _ => e
       | ABS (us, xs, e') => ABS (us, xs, imprisonVariable v (Coord.shiftRight coord, e'))
       | APP (theta, es) =>
           APP (theta, Spine.Functor.map (fn e => imprisonVariable v (coord, e)) es)

  fun liberateVariable v (coord, e) =
    case e of
         V (LN.FREE _, _) => e
       | ann as V (LN.BOUND coord', sigma) =>
           if Coord.Eq.eq (coord, coord') then V (LN.FREE v, sigma) else ann
       | ABS (us, xs, e) => ABS (us, xs, liberateVariable v (Coord.shiftRight coord, e))
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

  fun check (e, valence as ((symbols,variables), sigma)) =
    case e of
         `x =>
           let
             val () = assert "symbols not empty" (Spine.isEmpty symbols)
             val () = assert "variables not empty" (Spine.isEmpty variables)
           in
             V (LN.FREE x, sigma)
           end
       | (us, xs) \ e =>
           let
             val ((_, tau), _) = infer e
             val () = assertSortEq (sigma, tau)
           in
             ABS (Spine.Pair.zipEq (us, symbols), Spine.Pair.zipEq (xs, variables), imprisonVariables xs e)
           end
       | theta $ es =>
           let
             val () = assert "symbols not empty" (Spine.isEmpty symbols)
             val () = assert "variables not empty" (Spine.isEmpty variables)
             val (_, (valences, tau)) = Operator.proj theta
             val () = assertSortEq (sigma, tau)
             fun chkInf (e, valence) =
               let
                 val (valence', _) = infer e
                 val () = assertValenceEq (valence, valence')
               in
                 e
               end
             val theta' = Operator.Presheaf.map LN.FREE theta
           in
             APP (theta', Spine.Pair.mapEq chkInf (es, valences))
           end

  and infer (V (v, sigma)) =
      let
        val valence = ((Spine.empty (), Spine.empty ()), sigma)
      in
        (valence, ` (LN.getFree v))
      end
    | infer (ABS (Ypsilon, Gamma, e)) =
      let
        val us = Spine.Functor.map (Symbol.clone o #1) Ypsilon
        val xs = Spine.Functor.map (Variable.clone o #1) Gamma
        val ((symbols, variables), tau) = inferValence e
        val () = assert "variables not empty" (Spine.isEmpty variables)
        val () = assert "symbols not empty" (Spine.isEmpty symbols)
        val valence = ((Spine.Functor.map #2 Ypsilon, Spine.Functor.map #2 Gamma), tau)
      in
        (valence, (us, xs) \ liberateVariables xs e)
      end
    | infer (APP (theta, es)) =
      let
        val (_, (_, tau)) = Operator.proj theta
        val theta' = Operator.Presheaf.map LN.getFree theta
        val valence = ((Spine.empty (), Spine.empty ()), tau)
      in
        (valence, theta' $ es)
      end

  and inferValence (V (_, sigma)) = ((Spine.empty (), Spine.empty ()), sigma)
    | inferValence (ABS (Ypsilon, Gamma, e)) =
      let
        val (_, sigma) = inferValence e
        val symbolSorts = Spine.Functor.map #2 Ypsilon
        val variableSorts = Spine.Functor.map #2 Gamma
      in
        ((symbolSorts, variableSorts), sigma)
      end
    | inferValence (APP (theta, es)) =
      let
        val (_, (_, sigma)) = Operator.proj theta
      in
        ((Spine.empty (), Spine.empty ()), sigma)
      end

  structure Eq : EQ =
  struct
    type t = abt
    structure LnVarEq = LN.Eq (Variable.Eq)
    structure LnSymEq = LN.Eq (Symbol.Eq)
    structure OpLnEq = Operator.Eq (LnSymEq)
    structure OpEq = Operator.Eq (Symbol.Eq)
    fun eq (V (v, _), V (v', _)) = LnVarEq.eq (v, v')
      | eq (ABS (_, _, e), ABS (_, _, e')) = eq (e, e')
      | eq (APP (theta, es), APP (theta', es')) =
          OpLnEq.eq (theta, theta') andalso Spine.Pair.allEq eq (es, es')
      | eq _ = false
  end
end
