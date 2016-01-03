functor Union (Eq : EQ) =
struct
  fun elem (X, x) = List.exists (fn y => Eq.eq (x, y)) X
  fun union ([], Y) = Y
    | union (x :: X, Y) = if elem (Y, x) then union (X, Y) else x :: (union (X,  Y))
end

functor EqProj1 (type t structure Eq : EQ) =
struct
  type t = Eq.t * t
  fun eq ((a, _), (b, _)) = Eq.eq (a, b)
end

functor Abt
  (structure Symbol : SYMBOL
   structure Variable : SYMBOL
   structure Metavariable : PRESYMBOL
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
  structure Spine =
  struct
    open Valence.Spine Valence.Spine.Functor Valence.Spine.Foldable
  end

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
    local
      structure S = LocallyNameless (Coord)
    in
      open S S.Eq S.Functor S.Monad
    end

    type symbol = symbol t
    type operator = symbol Operator.t
    type variable = variable t
  end

  datatype abt =
      V of LN.variable * sort
    | APP of LN.operator * btm spine
    | META_APP of (metavariable * valence) * (LN.symbol * sort) spine * abt spine
  and btm = ABS of (symbol * sort) spine * (variable * sort) spine * abt

  (* Patterns for abstract binding trees. *)
  datatype 'a view =
      ` of variable
    | $ of operator * 'a bview spine
    | $# of metavariable * (symbol spine * 'a spine)
  and 'a bview =
     \ of (symbol spine * variable spine) * 'a

  infixr 5 \
  infix 5 $ $#

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

  local
    structure VS = Union (EqProj1 (type t = sort structure Eq = Symbol.Eq))
    structure VU = Union (EqProj1 (type t = sort structure Eq = Variable.Eq))
    structure MCtx = Metacontext
  in
    fun freeVariables M =
      let
        fun go R (V (LN.FREE v, sigma)) = VU.union ([(v, sigma)], R)
          | go R (APP (theta, Es)) =
              Spine.foldr VU.union R (Spine.map (go' []) Es)
          | go R (META_APP (m, us, Ms)) =
              Spine.foldr VU.union R (Spine.map (go []) Ms)
          | go R _ = R
        and go' R (ABS (_, _, M)) = go R M
      in
        go [] M
      end

    fun metacontext M =
      let
        fun go R (V _) = R
          | go R (APP (theta, Es)) =
              Spine.foldr MCtx.union R (Spine.map (go' MCtx.empty) Es)
          | go R (META_APP (mv, us, Ms)) =
              Spine.foldr MCtx.union (MCtx.extend R mv) (Spine.map (go MCtx.empty) Ms)
        and go' R (ABS (_, _, M)) = go R M
      in
        go MCtx.empty M
      end

    fun freeSymbols M =
      let
        fun opFreeSymbols theta =
          let
            val Ypsilon = Operator.support theta
          in
            List.foldl (fn ((u, sigma), R) => ((LN.getFree u, sigma) :: R) handle _ => R) [] Ypsilon
          end
        fun go R (APP (theta, Es)) =
              VS.union (opFreeSymbols theta, Spine.foldr VS.union R (Spine.map (go' []) Es))
          | go R (META_APP (m, us, Ms)) =
              VS.union
                (Spine.foldr (fn ((u, sigma), X) => (LN.getFree u, sigma) :: X handle _ => X) [] us,
                 Spine.foldr VS.union R (Spine.map (go []) Ms))
          | go R _ = R
        and go' R (ABS (us, _, M)) = go R M
      in
        go [] M
      end

  end

  fun subst (N, x) M =
    case M of
         V (LN.FREE y, sigma) => if Variable.Eq.eq (x, y) then N else M
       | V _ => M
       | APP (theta, Es) =>
           APP (theta, Spine.map (substBtm (N, x)) Es)
       | META_APP (m, us, Ms) =>
           META_APP (m, us, Spine.map (subst (N, x)) Ms)
  and substBtm (N, x) (ABS (us, xs, M)) =
    ABS (us, xs, subst (N, x) M)

  fun rename (v, u) =
    let
      fun go M =
        case M of
             V _ => M
           | APP (theta, Es) =>
             let
               fun rho u' = if Symbol.Eq.eq (u, u') then v else u'
               val theta' = Operator.Presheaf.map (LN.map rho) theta
             in
               APP (theta', Spine.map go' Es)
             end
           | META_APP (m, us, Ms) =>
               let
                 fun rho u' = if Symbol.Eq.eq (u, u') then v else u'
                 fun rho' (l, s) = (LN.map rho l, s)
               in
                 META_APP (m, Spine.map rho' us, Spine.map go Ms)
               end
      and go' (ABS (us, vs, M)) = ABS (us, vs, go M)
    in
      fn M =>
        if List.exists (fn (v', _) => Symbol.Eq.eq (v', v)) (freeSymbols M) then
          raise Fail "Renaming fails to preserve apartness"
        else
          go M
    end

  fun imprisonVariable (v, tau) (coord, M) =
    case M of
         V (LN.FREE v', sigma) =>
           if Variable.Eq.eq (v, v') then
             (assertSortEq (sigma, tau);
              V (LN.BOUND coord, sigma))
           else
             M
       | V _ => M
       | APP (theta, Es) =>
           APP (theta, Spine.map (fn N => imprisonVariableBtm (v, tau) (coord, N)) Es)
       | META_APP (m, us, Ms) =>
           META_APP (m, us, Spine.map (fn N => imprisonVariable (v, tau) (coord, N)) Ms)
  and imprisonVariableBtm (v, tau) (coord, ABS (us, xs, M)) =
    ABS (us, xs, imprisonVariable (v, tau) (Coord.shiftRight coord, M))

  fun imprisonSymbol (v, tau) (coord, M) =
    case M of
         V _ => M
       | APP (theta, Es) =>
         let
           fun rho v' = if Symbol.Eq.eq (v, v') then LN.BOUND coord else LN.FREE v'
           fun chk (LN.FREE v', tau') = if Symbol.Eq.eq (v, v') then assertSortEq (tau, tau') else ()
             | chk _ = ()
           val _ = List.app chk (Operator.support theta)
           val theta' = Operator.Presheaf.map (LN.bind rho) theta
         in
           APP (theta', Spine.map (fn E => imprisonSymbolBtm (v, tau) (coord, E)) Es)
         end
       | META_APP (m, us, Ms) =>
         let
           fun rho v' = if Symbol.Eq.eq (v, v') then LN.BOUND coord else LN.FREE v'
           fun rho' (l, s) = (LN.bind rho l, s)
           val vs = Spine.map rho' us
         in
           META_APP (m, vs, Spine.map (fn N => imprisonSymbol (v, tau) (coord, N)) Ms)
         end
  and imprisonSymbolBtm (v, tau) (coord, ABS (us, xs, M)) =
    ABS (us, xs, imprisonSymbol (v, tau) (Coord.shiftRight coord, M))


  fun liberateVariable v (coord, e) =
    case e of
         V (LN.FREE _, _) => e
       | V (LN.BOUND coord', sigma) =>
           if Coord.Eq.eq (coord, coord') then V (LN.FREE v, sigma) else e
       | APP (theta, es) =>
           APP (theta, Spine.map (fn e => liberateVariableBtm v (coord, e)) es)
       | META_APP (m, us, Ms) =>
           META_APP (m, us, Spine.map (fn e => liberateVariable v (coord, e)) Ms)
  and liberateVariableBtm v (coord, ABS (us, xs, M)) =
    ABS (us, xs, liberateVariable v (Coord.shiftRight coord, M))


  fun liberateSymbol v (coord, e) =
    case e of
         V _ => e
       | APP (theta, es) =>
         let
           fun rho (LN.BOUND coord') =
               if Coord.Eq.eq (coord, coord') then LN.FREE v else LN.BOUND coord'
             | rho v' = v'
           val theta' = Operator.Presheaf.map rho theta
         in
           APP (theta', Spine.map (fn e => liberateSymbolBtm v (coord, e)) es)
         end
       | META_APP (m, us, Ms) =>
         let
           fun rho (LN.BOUND coord') =
               if Coord.Eq.eq (coord, coord') then LN.FREE v else LN.BOUND coord'
             | rho v' = v'
           fun rho' (l, s) = (rho l, s)
           val vs = Spine.map rho' us
         in
           META_APP (m, vs, Spine.map (fn e => liberateSymbol v (coord, e)) Ms)
         end
  and liberateSymbolBtm v (coord, ABS (us, xs, M)) =
    ABS (us, xs, liberateSymbol v (Coord.shiftRight coord, M))

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
    fun imprisonVariables (vs, sorts) t =
      let
        val Gamma = Spine.Pair.zipEq (vs, sorts)
      in
        ShiftFoldMap.foldMap imprisonVariable Gamma (Coord.origin, t)
      end

    fun imprisonSymbols (vs, sorts) t =
      let
        val Upsilon = Spine.Pair.zipEq (vs, sorts)
      in
        ShiftFoldMap.foldMap imprisonSymbol Upsilon (Coord.origin, t)
      end

    fun liberateVariables vs t =
      ShiftFoldMap.foldMap liberateVariable vs (Coord.origin, t)

    fun liberateSymbols vs t =
      ShiftFoldMap.foldMap liberateSymbol vs (Coord.origin, t)
  end

  fun metasubst (E, mv) M =
    case M of
         V _ => M
       | APP (theta, Es) =>
           APP (theta, Spine.map (metasubstBtm (E, mv)) Es)
       | META_APP ((mv', valence), us, Ms) =>
           if Metavariable.Eq.eq (mv, mv') then
             let
               val ABS (Upsilon, Gamma, M) = E
               val us = Spine.map #1 Upsilon
               val xs = Spine.map #1 Gamma
               val M' = liberateVariables xs (liberateSymbols us M)
               val env = Spine.Pair.zipEq (Ms, xs)
             in
               Spine.foldr (fn (s, M) => subst s M) M' env
             end
           else
             META_APP ((mv', valence), us, Spine.map (metasubst (E, mv)) Ms)
  and metasubstBtm (E, mv) (ABS (us, xs, M)) =
    ABS (us, xs, metasubst (E, mv) M)

  fun checkb Theta ((us, xs) \ M, ((ssorts, vsorts), sigma)) =
    let
      val (_, tau) = infer M
      val () = assertSortEq (sigma, tau)
    in
      ABS (Spine.Pair.zipEq (us, ssorts),
           Spine.Pair.zipEq (xs, vsorts),
           imprisonSymbols (us, ssorts) (imprisonVariables (xs, vsorts) M))
    end

  and infer M =
    case M of
         V (x, tau) => (` (LN.getFree x), tau)
       | APP (theta, Es) =>
         let
           val (_, tau) = Operator.arity theta
           val theta' = Operator.Presheaf.map LN.getFree theta
           val Es' = Spine.map (#1 o inferb) Es
         in
           (theta' $ Es', tau)
         end
       | META_APP ((mv, (_, tau)), us, Ms) =>
         let
           val us' = Spine.map (LN.getFree o #1) us
         in
           (mv $# (us', Ms), tau)
         end

  and check Theta (M, sigma) =
    case M of
         `x => V (LN.FREE x, sigma)
       | theta $ Es =>
           let
             val (valences, tau)  = Operator.arity theta
             val () = assertSortEq (sigma, tau)
             val theta' = Operator.Presheaf.map LN.FREE theta
             val Es' = Spine.Pair.mapEq (checkb Theta) (Es, valences)
           in
             APP (theta', Es')
           end
       | mv $# (us, Ms) =>
           let
             val valence as ((ssorts, vsorts), tau) = Metacontext.lookup Theta mv
             val () = assertSortEq (sigma, tau)
             val us' = Spine.Pair.zipEq (Spine.map LN.FREE us, ssorts)
             fun chkInf (M, tau) =
               let
                 val (_, tau') = infer M
               in
                 assertSortEq (tau, tau'); M
               end
             val Ms' = Spine.Pair.mapEq chkInf (Ms, vsorts)
           in
             META_APP ((mv, valence), us', Ms')
           end

  and inferb (ABS (Upsilon, Gamma, M)) =
    let
      val us = Spine.map (Symbol.clone o #1) Upsilon
      val xs = Spine.map (Variable.clone o #1) Gamma
      val M' = liberateSymbols us (liberateVariables xs M)
      val (_, tau) = infer M'
      val valence = ((Spine.map #2 Upsilon, Spine.map #2 Gamma), tau)
    in
      ((us, xs) \ M',
       valence)
    end


  structure BFunctor =
  struct
    type 'a t = 'a bview
    fun map f ((us, xs) \ M) =
      (us, xs) \ f M
  end

  structure Functor =
  struct
    type 'a t = 'a view
    fun map f M =
      case M of
           `x => `x
         | theta $ Es =>
             theta $ Spine.map (BFunctor.map f) Es
         | mv $# (us, Ms) =>
              mv $# (us, Spine.map f Ms)
  end


  structure Eq : EQ =
  struct
    type t = abt

    structure OpLnEq =
    struct
      val eq = Operator.Eq.eq (LN.eq Symbol.Eq.eq)
    end

    structure OpEq =
    struct
      val eq = Operator.Eq.eq Symbol.Eq.eq
    end

    fun eq (V (v, _), V (v', _)) = LN.eq Variable.Eq.eq (v, v')
      | eq (APP (theta, es), APP (theta', es')) =
          OpLnEq.eq (theta, theta') andalso Spine.Pair.allEq eq' (es, es')
      | eq (META_APP ((mv, _), us, es), META_APP ((mv', _), us', es')) =
          Metavariable.Eq.eq (mv, mv')
            andalso Spine.Pair.allEq (fn ((x, _), (y, _)) => LN.eq Symbol.Eq.eq (x,y)) (us, us')
            andalso Spine.Pair.allEq eq (es, es')
      | eq _ = false
    and eq' (ABS (_, _, e), ABS (_, _, e')) = eq (e, e')
  end
end
