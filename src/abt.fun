functor Abt
  (structure Symbol : SYMBOL
   structure Variable : SYMBOL
   structure Metavariable : SYMBOL
   structure Operator : OPERATOR
   structure Metacontext : METACONTEXT
     where type metavariable = Metavariable.t
     where type valence = Operator.Arity.Valence.t) : ABT =
struct

  structure Symbol = Symbol
    and Variable = Variable
    and Metavariable = Metavariable
    and Operator = Operator
    and Arity = Operator.Arity
    and Metacontext = Metacontext

  structure Sort = Arity.Sort and Valence = Arity.Valence
  structure Spine = Valence.Spine

  type symbol = Symbol.t
  type variable = Variable.t
  type metavariable = Metavariable.t
  type metacontext = Metacontext.t

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

    structure Monad : MONAD =
    struct
      type 'a t = 'a t
      fun pure v = FREE v
      fun bind f (FREE v) = f v
        | bind f (BOUND i) = BOUND i
    end
  end

  datatype abt =
      V of LN.variable * sort
    | ABS of (symbol * sort) spine * (variable * sort) spine * abt
    | APP of LN.operator * abt spine
    | META_APP of metavariable * (LN.symbol * sort) spine * abt spine

  datatype 'a view =
      ` of variable
    | $ of operator * 'a spine
    | $# of metavariable * (symbol spine * 'a spine)
    | \ of (symbol spine * variable spine) * 'a

  infixr 5 \
  infix 5 $ $#

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
          | go R (META_APP (m, us, Ms)) =
              Spine.Foldable.foldr VU.union R (Spine.Functor.map (go []) Ms)
          | go R _ = R
      in
        go [] M
      end

    fun freeSymbols M =
      let
        fun opFreeSymbols theta =
          let
            val Ypsilon = Operator.support theta
          in
            List.foldl (fn ((u, _), R) => (LN.getFree u :: R) handle _ => R) [] Ypsilon
          end
        fun go R (ABS (_, _, M)) = go R M
          | go R (APP (theta, Es)) =
              VS.union (opFreeSymbols theta, Spine.Foldable.foldr VS.union R (Spine.Functor.map (go []) Es))
          | go R (META_APP (m, us, Ms)) =
              VS.union
                (Spine.Foldable.foldr (fn ((u, _), X) => LN.getFree u :: X handle _ => X) [] us,
                 Spine.Foldable.foldr VS.union R (Spine.Functor.map (go []) Ms))
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
       | META_APP (m, us, Ms) =>
           META_APP (m, us, Spine.Functor.map (subst (N, x)) Ms)

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
           | META_APP (m, us, Ms) =>
               let
                 fun rho u' = if Symbol.Eq.eq (u, u') then v else u'
                 fun rho' (l, s) = (LN.Functor.map rho l, s)
               in
                 META_APP (m, Spine.Functor.map rho' us, Spine.Functor.map go Ms)
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
       | m $# (us, Ms) => m $# (us, Spine.Functor.map f Ms)
  end

  fun imprisonVariable v (coord, e) =
    case e of
         V (LN.FREE v', sigma) =>
           if Variable.Eq.eq (v, v') then V (LN.BOUND coord, sigma) else e
       | V _ => e
       | ABS (us, xs, e') => ABS (us, xs, imprisonVariable v (Coord.shiftRight coord, e'))
       | APP (theta, es) =>
           APP (theta, Spine.Functor.map (fn e => imprisonVariable v (coord, e)) es)
       | META_APP (m, us, es) =>
           META_APP (m, us, Spine.Functor.map (fn e => imprisonVariable v (coord, e)) es)

  fun imprisonSymbol v (coord, e) =
    case e of
         V _ => e
       | ABS (us, xs, e') => ABS (us, xs, imprisonSymbol v (Coord.shiftRight coord, e'))
       | APP (theta, es) =>
         let
           fun rho v' = if Symbol.Eq.eq (v, v') then LN.BOUND coord else LN.FREE v'
           val theta' = Operator.Presheaf.map (LN.Monad.bind rho) theta
         in
           APP (theta', Spine.Functor.map (fn e => imprisonSymbol v (coord, e)) es)
         end
       | META_APP (m, us, Ms) =>
         let
           fun rho v' = if Symbol.Eq.eq (v, v') then LN.BOUND coord else LN.FREE v'
           fun rho' (l, s) = (LN.Monad.bind rho l, s)
           val vs = Spine.Functor.map rho' us
         in
           META_APP (m, vs, Spine.Functor.map (fn e => imprisonSymbol v (coord, e)) Ms)
         end

  fun liberateVariable v (coord, e) =
    case e of
         V (LN.FREE _, _) => e
       | ann as V (LN.BOUND coord', sigma) =>
           if Coord.Eq.eq (coord, coord') then V (LN.FREE v, sigma) else ann
       | ABS (us, xs, e) => ABS (us, xs, liberateVariable v (Coord.shiftRight coord, e))
       | APP (theta, es) =>
           APP (theta, Spine.Functor.map (fn e => liberateVariable v (coord, e)) es)
       | META_APP (m, us, Ms) =>
           META_APP (m, us, Spine.Functor.map (fn e => liberateVariable v (coord, e)) Ms)

  fun liberateSymbol v (coord, e) =
    case e of
         V _ => e
       | ABS (us, xs, e) => ABS (us, xs, liberateSymbol v (Coord.shiftRight coord, e))
       | APP (theta, es) =>
         let
           fun rho (LN.BOUND coord') =
               if Coord.Eq.eq (coord, coord') then LN.FREE v else LN.BOUND coord'
             | rho v' = v'
           val theta' = Operator.Presheaf.map rho theta
         in
           APP (theta', Spine.Functor.map (fn e => liberateSymbol v (coord, e)) es)
         end
       | META_APP (m, us, Ms) =>
         let
           fun rho (LN.BOUND coord') =
               if Coord.Eq.eq (coord, coord') then LN.FREE v else LN.BOUND coord'
             | rho v' = v'
           fun rho' (l, s) = (rho l, s)
           val vs = Spine.Functor.map rho' us
         in
           META_APP (m, vs, Spine.Functor.map (fn e => liberateSymbol v (coord, e)) Ms)
         end


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

    fun imprisonSymbols vs t =
      ShiftFoldMap.foldMap imprisonSymbol vs (Coord.origin, t)

    fun liberateVariables vs t =
      ShiftFoldMap.foldMap liberateVariable vs (Coord.origin, t)

    fun liberateSymbols vs t =
      ShiftFoldMap.foldMap liberateSymbol vs (Coord.origin, t)
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

  fun check Omega (e, valence as ((symbols,variables), sigma)) =
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
             val ((_, tau), _) = infer Omega e
             val () = assertSortEq (sigma, tau)
           in
             ABS (Spine.Pair.zipEq (us, symbols),
                  Spine.Pair.zipEq (xs, variables),
                  imprisonSymbols us (imprisonVariables xs e))
           end
       | theta $ es =>
           let
             val () = assert "symbols not empty" (Spine.isEmpty symbols)
             val () = assert "variables not empty" (Spine.isEmpty variables)
             val (valences, tau) = Operator.arity theta
             val () = assertSortEq (sigma, tau)
             fun chkInf (e, valence) =
               let
                 val (valence', _) = infer Omega e
                 val () = assertValenceEq (valence, valence')
               in
                 e
               end
             val theta' = Operator.Presheaf.map LN.FREE theta
           in
             APP (theta', Spine.Pair.mapEq chkInf (es, valences))
           end

       | m $# (us, Ms) =>
           let
             val () = assert "symbols not empty" (Spine.isEmpty symbols)
             val () = assert "variables not empty" (Spine.isEmpty variables)
             val ((symbolSorts, termSorts), tau) = Metacontext.lookup Omega m
           in
             raise Match
           end

  and infer _ (V (v, sigma)) =
      let
        val valence = ((Spine.empty (), Spine.empty ()), sigma)
      in
        (valence, ` (LN.getFree v))
      end
    | infer Omega (ABS (Ypsilon, Gamma, e)) =
      let
        val us = Spine.Functor.map (Symbol.clone o #1) Ypsilon
        val xs = Spine.Functor.map (Variable.clone o #1) Gamma
        val ((symbols, variables), tau) = inferValence Omega e
        val () = assert "variables not empty" (Spine.isEmpty variables)
        val () = assert "symbols not empty" (Spine.isEmpty symbols)
        val valence = ((Spine.Functor.map #2 Ypsilon, Spine.Functor.map #2 Gamma), tau)
      in
        (valence, (us, xs) \ liberateSymbols us (liberateVariables xs e))
      end
    | infer _ (APP (theta, es)) =
      let
        val (_, tau) = Operator.arity theta
        val theta' = Operator.Presheaf.map LN.getFree theta
        val valence = ((Spine.empty (), Spine.empty ()), tau)
      in
        (valence, theta' $ es)
      end
    | infer Omega (META_APP (mv, us, es)) =
      let
        val (_, tau) = Metacontext.lookup Omega mv
        val valence = ((Spine.empty (), Spine.empty ()), tau)
        val us' = Spine.Functor.map (LN.getFree o #1) us
      in
        (valence, mv $# (us', es))
      end

  and inferValence _ (V (_, sigma)) = ((Spine.empty (), Spine.empty ()), sigma)
    | inferValence Omega (ABS (Ypsilon, Gamma, e)) =
      let
        val (_, sigma) = inferValence Omega e
        val symbolSorts = Spine.Functor.map #2 Ypsilon
        val variableSorts = Spine.Functor.map #2 Gamma
      in
        ((symbolSorts, variableSorts), sigma)
      end
    | inferValence _ (APP (theta, es)) =
      let
        val (_, sigma) = Operator.arity theta
      in
        ((Spine.empty (), Spine.empty ()), sigma)
      end
    | inferValence Omega (META_APP (mv, us, es)) =
      let
        val (_, tau) = Metacontext.lookup Omega mv
      in
        ((Spine.empty (), Spine.empty ()), tau)
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
