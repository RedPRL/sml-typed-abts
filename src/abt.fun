functor Abt
  (structure Symbol : SYMBOL
   structure Variable : SYMBOL
   structure Metavariable : PRESYMBOL
   structure Operator : OPERATOR) : ABT =
struct
  structure Symbol = Symbol
    and Variable = Variable
    and Metavariable = Metavariable
    and Operator = Operator
    and Arity = Operator.Arity

  structure Sort = Arity.Valence.Sort and Valence = Arity.Valence
  structure Spine = Valence.Spine

  structure MetaCtx = SplayDict (structure Key = Metavariable)
  structure VarCtx = SplayDict (structure Key = Variable)
  structure SymCtx = SplayDict (structure Key = Symbol)

  type sort = Sort.t
  type valence = Valence.t
  type coord = Coord.t
  type symbol = Symbol.t
  type variable = Variable.t
  type metavariable = Metavariable.t
  type operator = symbol Operator.t
  type 'a spine = 'a Spine.t

  structure LN =
  struct
    local structure S = LocallyNameless (Coord) in open S end
    type symbol = symbol t
    type operator = symbol Operator.t
    type variable = variable t
  end

  (* Note that we use LN.variable so V may work with both free and bound
   * variables and LN.operator/symbols to distinguish free and bound symbols.
   * Otherwise this is almost the same as a pattern except that
   * we annotate things with sorts/valences so that we can always determine sorts
   * without a context
   *)
  datatype abt =
      V of LN.variable * sort
    | APP of LN.operator * abs spine
    | META_APP of (metavariable * valence) * (LN.symbol * sort) spine * abt spine
  and abs = ABS of (symbol * sort) spine * (variable * sort) spine * abt

  type metactx = valence MetaCtx.dict
  type varctx = sort VarCtx.dict
  type symctx = sort SymCtx.dict

  type metaenv = abs MetaCtx.dict
  type varenv = abt VarCtx.dict
  type symenv = symbol SymCtx.dict

  fun mapAbs f (ABS (us, xs, m)) =
    ABS (us, xs, f m)

  fun abtToAbs m =
    ABS (Spine.empty (), Spine.empty (), m)

  (* Patterns for abstract binding trees. *)
  datatype 'a view =
      ` of variable
    | $ of operator * 'a bview spine
    | $# of metavariable * (symbol spine * 'a spine)
  and 'a bview =
     \ of (symbol spine * variable spine) * 'a

  infixr 5 \
  infix 5 $ $#

  (* A family of convenience functions for failing when things go wrong.
   * These are internal checks and so they should raise Fail; people shouldn't
   * be trying to catch these.
   *)
  fun assert msg b =
    if b then () else raise Fail msg

  fun assertSortEq (sigma, tau) =
    assert
      ("expected " ^ Sort.toString sigma ^ " == " ^ Sort.toString tau)
      (Sort.eq (sigma, tau))

  fun assertValenceEq (v1, v2) =
    assert
      ("expected " ^ Valence.toString v1 ^ " == " ^ Valence.toString v2)
      (Valence.eq (v1, v2))

  (* All of the *ctx operations are implemented in much the same way. The
   * term is traversed and each time we reach the object we're searching for
   * (like (V (LN.FREE v, sigma))) we tack it on to the growing collection
   * of previously found items. The actual algorithm for ensuring we don't
   * duplicate everything is contained in [Union] or the implementation of
   * MetaCtx.
   *
   * Note that we already have all the type information already lying around
   * in the term so producing it is free! Also note that variables/symbols are
   * locally marked as free or not so we needn't carry around a table to understand
   * binding.
   *)


  local
    structure MetaCtxUtil = ContextUtil (structure Ctx = MetaCtx and Elem = Valence)
  in
    fun metactx M =
      let
        fun go R =
          fn V _ => R
           | APP (theta, Es) =>
               Spine.foldr MetaCtxUtil.union R (Spine.map (go' MetaCtx.empty) Es)
           | META_APP (mv, us, Ms) =>
               Spine.foldr MetaCtxUtil.union (MetaCtxUtil.extend R mv) (Spine.map (go MetaCtx.empty) Ms)
        and go' R (ABS (_, _, M)) = go R M
      in
        go MetaCtx.empty M
      end
  end

  local
    structure VarCtxUtil = ContextUtil (structure Ctx = VarCtx and Elem = Sort)
  in
    fun varctx M =
      let
        fun go R =
          fn V (LN.FREE v, sigma) =>
               VarCtxUtil.extend R (v, sigma)
           | APP (theta, Es) =>
               Spine.foldr VarCtxUtil.union R (Spine.map (go' VarCtx.empty) Es)
           | META_APP (m, us, Ms) =>
               Spine.foldr VarCtxUtil.union R (Spine.map (go VarCtx.empty) Ms)
           | _ => R
        and go' R (ABS (_, _, M)) = go R M
      in
        go VarCtx.empty M
      end
  end

  local
    structure SymCtxUtil = ContextUtil (structure Ctx = SymCtx and Elem = Sort)
  in
    fun symctx M =
      let
        fun tryExtendFree R (u, sigma) =
          SymCtxUtil.extend R (LN.getFree u, sigma)
            handle _ => R

        fun opSupport theta =
          List.foldl
            (fn ((u, sigma), R) => tryExtendFree R (u, sigma))
            SymCtx.empty
            (Operator.support theta)

        fun go R =
          fn APP (theta, Es) =>
               Spine.foldr
                 SymCtxUtil.union
                 (SymCtxUtil.union (R, opSupport theta))
                 (Spine.map (go' SymCtx.empty) Es)
           | META_APP (m, us, Ms) =>
               SymCtxUtil.union
                 (Spine.foldr (fn ((u, sigma), X) => tryExtendFree X (u, sigma)) SymCtx.empty us,
                  Spine.foldr SymCtxUtil.union R (Spine.map (go SymCtx.empty) Ms))
           | _ => R
        and go' R (ABS (_, _, M)) = go R M
      in
        go SymCtx.empty M
      end
  end

  fun liftTraverseAbs f coord (ABS (us, xs, M)) =
    ABS (us, xs, f (Coord.shiftRight coord) M)

  fun mapAbs f (ABS (us, xs, M)) =
    ABS (us, xs, f M)

  (* This function takes a variable and its sort and switches it to a
   * bound variable. In this process we also
   *
   *  - Check that the supplied sort is actually the correct sort of the variable
   *  - Drag the coordinate given so that the bound variable is annotated with the
   *    correct position in the term.
   *)
  fun imprisonVariable (v, tau) coord =
    fn m as V (LN.FREE v', sigma) =>
         if Variable.eq (v, v') then
           (assertSortEq (sigma, tau);
            V (LN.BOUND coord, sigma))
         else
           m
     | V v => V v
     | APP (theta, es) =>
         APP (theta, Spine.map (liftTraverseAbs (imprisonVariable (v, tau)) coord) es)
     | META_APP (m, us, ms) =>
         META_APP (m, us, Spine.map (imprisonVariable (v, tau) coord) ms)

  fun imprisonSymbol (v, tau) coord =
    fn V v => V v
     | APP (theta, Es) =>
         let
           fun rho v' = if Symbol.eq (v, v') then LN.BOUND coord else LN.FREE v'
           fun chk (LN.FREE v', tau') = if Symbol.eq (v, v') then assertSortEq (tau, tau') else ()
             | chk _ = ()
           val _ = List.app chk (Operator.support theta)
           val theta' = Operator.map (LN.bind rho) theta
         in
           APP (theta', Spine.map (liftTraverseAbs (imprisonSymbol (v,tau)) coord) Es)
         end
     | META_APP (m, us, Ms) =>
         let
           fun rho v' = if Symbol.eq (v, v') then LN.BOUND coord else LN.FREE v'
           fun rho' (l, s) = (LN.bind rho l, s)
           val vs = Spine.map rho' us
         in
           META_APP (m, vs, Spine.map (imprisonSymbol (v, tau) coord) Ms)
         end

  (* This is the reverse of the above, given a position we hunt around for
   * a bound variable in the correct slot and switch out for a free one.
   *)
  fun liberateVariable v coord =
    fn e as V (LN.FREE _, _) => e
     | e as V (LN.BOUND coord', sigma) =>
         if Coord.eq (coord, coord') then V (LN.FREE v, sigma) else e
     | APP (theta, es) =>
         APP (theta, Spine.map (liftTraverseAbs (liberateVariable v) coord) es)
     | META_APP (x, us, ms) =>
         META_APP (x, us, Spine.map (liberateVariable v coord) ms)

  fun liberateSymbol u coord =
    let
      fun rho (LN.BOUND coord') = if Coord.eq (coord, coord') then LN.FREE u else LN.BOUND coord'
        | rho u' = u'
    in
      fn e as V _ => e
       | APP (theta, es) =>
           let
             val theta' = Operator.map rho theta
             val fs = Spine.map (liftTraverseAbs (liberateSymbol u) coord) es
           in
             APP (theta', fs)
           end
       | META_APP (x, us, ms) =>
           let
             val vs = Spine.map (fn (l,s) => (rho l, s)) us
             val ns = Spine.map (liberateSymbol u coord) ms
           in
            META_APP (x, vs, ns)
           end
    end

  (* A pluralized version of all of the above functions. The foldStar
   * machinery is used to propogate the coord correctly through
   * all of these calls. The functions are set up so that each bound/freed
   * variable comes from the same abstraction.
   *)
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
         structure F = Spine)

    fun foldStar f xs t =
      ShiftFoldMap.foldMap
        (fn v => fn (c, M) => f v c M)
        xs
        (Coord.origin, t)
  in
    val imprisonVariables = foldStar imprisonVariable o Spine.Pair.zipEq
    val imprisonSymbols = foldStar imprisonSymbol o Spine.Pair.zipEq
    val liberateVariables = foldStar liberateVariable
    val liberateSymbols = foldStar liberateSymbol
  end

  fun metasubstEnv rho =
    fn m as V _ => m
     | APP (theta, es) =>
         APP (theta, Spine.map (mapAbs (metasubstEnv rho)) es)
    | META_APP ((mv, valence), us, ms) =>
        let
          val ms' = Spine.map (metasubstEnv rho) ms
        in
          case MetaCtx.find rho mv of
              SOME (ABS (upsilon, gamma, m)) =>
                let
                  val us = Spine.map #1 upsilon
                  val xs = Spine.map #1 gamma
                  val m' = liberateVariables xs (liberateSymbols us m)
                  val rho' =
                    Spine.foldr
                      (fn ((x,m), rho) => VarCtx.insert rho x m)
                      VarCtx.empty
                      (Spine.Pair.zipEq (xs, ms'))
                in
                  substEnv rho' m'
                end
            | NONE => META_APP ((mv, valence), us, ms')
        end

  and substEnv rho =
    fn m as V (LN.FREE x, sigma) => getOpt (VarCtx.find rho x, m)
     | m as V _ => m
     | APP (theta, es) => APP (theta, Spine.map (mapAbs (substEnv rho)) es)
     | META_APP (m, us, ms) => META_APP (m, us, Spine.map (substEnv rho) ms)

  fun renameEnv rho =
    fn m as V _ => m
     | APP (theta, es) =>
         let
           fun ren u = getOpt (SymCtx.find rho u, u)
           val theta' = Operator.map (LN.map ren) theta
         in
           APP (theta', Spine.map (mapAbs (renameEnv rho)) es)
         end
     | META_APP (x, us, ms) =>
         let
           fun ren u = getOpt (SymCtx.find rho u, u)
           fun ren' (l,s) = (LN.map ren l, s)
         in
           META_APP (x, Spine.map ren' us, Spine.map (renameEnv rho) ms)
         end

  fun subst (n, x) = substEnv (VarCtx.insert VarCtx.empty x n)
  fun metasubst (e, mv) = metasubstEnv (MetaCtx.insert MetaCtx.empty mv e)
  fun rename (v, u) = renameEnv (SymCtx.insert SymCtx.empty u v)

  fun checkb psi ((us, xs) \ m, ((ssorts, vsorts), sigma)) =
    let
      val (_, tau) = infer m
      val () = assertSortEq (sigma, tau)
    in
      ABS
        (Spine.Pair.zipEq (us, ssorts),
         Spine.Pair.zipEq (xs, vsorts),
         imprisonSymbols (us, ssorts) (imprisonVariables (xs, vsorts) m))
    end

  and infer M =
    case M of
         V (x, tau) => (` (LN.getFree x), tau)
       | APP (theta, Es) =>
         let
           val (_, tau) = Operator.arity theta
           val theta' = Operator.map LN.getFree theta
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

  and inferb (ABS (upsilon, gamma, M)) =
    let
      val us = Spine.map (Symbol.clone o #1) upsilon
      val xs = Spine.map (Variable.clone o #1) gamma
      val M' = liberateSymbols us (liberateVariables xs M)
      val (_, tau) = infer M'
      val valence = ((Spine.map #2 upsilon, Spine.map #2 gamma), tau)
    in
      ((us, xs) \ M',
       valence)
    end

  val out = #1 o infer
  val sort = #2 o infer
  val outb = #1 o inferb
  val valence = #2 o inferb

  fun check psi (m, sigma) =
    case m of
         `x => V (LN.FREE x, sigma)
       | theta $ es =>
           let
             val (valences, tau)  = Operator.arity theta
             val () = assertSortEq (sigma, tau)
             val theta' = Operator.map LN.FREE theta
             val es' = Spine.Pair.mapEq (checkb psi) (es, valences)
           in
             APP (theta', es')
           end
       | mv $# (us, ms) =>
           let
             val valence as ((ssorts, vsorts), tau) = MetaCtx.lookup psi mv
             val () = assertSortEq (sigma, tau)
             val us' = Spine.Pair.zipEq (Spine.map LN.FREE us, ssorts)
             fun chkInf (m, tau) =
               (assertSortEq (tau, sort m); m)
             val ms' = Spine.Pair.mapEq chkInf (ms, vsorts)
           in
             META_APP ((mv, valence), us', ms')
           end


  val check' = check MetaCtx.empty
  val checkb' = checkb MetaCtx.empty


  fun mapb f ((us, xs) \ M) =
    (us, xs) \ f M

  fun map f =
    fn `x => `x
     | theta $ es =>
         theta $ Spine.map (mapb f) es
     | mv $# (us, ms) =>
         mv $# (us, Spine.map f ms)

  local
    structure OpLnEq = struct val eq = Operator.eq (LN.eq Symbol.eq) end
  in
    (* While this looks simple by using locally nameless representations this
     * implements alpha equivalence (and is very efficient!)
     *)
    fun eq (V (v, _), V (v', _)) = LN.eq Variable.eq (v, v')
      | eq (APP (theta, es), APP (theta', es')) =
          OpLnEq.eq (theta, theta') andalso Spine.Pair.allEq eqAbs (es, es')
      | eq (META_APP ((mv, _), us, es), META_APP ((mv', _), us', es')) =
          Metavariable.eq (mv, mv')
            andalso Spine.Pair.allEq (fn ((x, _), (y, _)) => LN.eq Symbol.eq (x,y)) (us, us')
            andalso Spine.Pair.allEq eq (es, es')
      | eq _ = false
    and eqAbs (ABS (_, _, e), ABS (_, _, e')) = eq (e, e')
  end
end

functor SimpleAbt (Operator : OPERATOR) =
  Abt (structure Symbol = Symbol ()
       structure Variable = Symbol ()
       structure Metavariable = Symbol ()
       structure Operator = Operator)
