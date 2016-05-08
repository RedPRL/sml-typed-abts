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

  type metactx = valence MetaCtx.dict
  type varctx = sort VarCtx.dict
  type symctx = sort SymCtx.dict

  type ctx = metactx * symctx * varctx

  structure Ctx =
  struct
    structure MetaCtxUtil = ContextUtil (structure Ctx = MetaCtx and Elem = Valence)
    structure VarCtxUtil = ContextUtil (structure Ctx = VarCtx and Elem = Sort)
    structure SymCtxUtil = ContextUtil (structure Ctx = SymCtx and Elem = Sort)

    val empty =
      (MetaCtx.empty,
       SymCtx.empty,
       VarCtx.empty)

    fun merge ((mctx1, sctx1, vctx1), (mctx2, sctx2, vctx2)) =
      let
        val mctx = MetaCtxUtil.union (mctx1, mctx2)
        val sctx = SymCtxUtil.union (sctx1, sctx2)
        val vctx = VarCtxUtil.union (vctx1, vctx2)
      in
        (mctx, sctx, vctx)
      end

    fun modifyMetas f (mctx, sctx, vctx) =
      (f mctx, sctx, vctx)

    fun modifySyms f (mctx, sctx, vctx) =
      (mctx, f sctx, vctx)

    fun modifyVars f (mctx, sctx, vctx) =
      (mctx, sctx, f vctx)
  end

  datatype 'a ann = <: of 'a * (metactx * symctx * varctx)
  infix <:

  (* Note that we use LN.variable so V may work with both free and bound
   * variables and LN.operator/symbols to distinguish free and bound symbols.
   * Otherwise this is almost the same as a pattern except that
   * we annotate things with sorts/valences so that we can always determine sorts
   * without a context
   *)
  datatype abt =
      V of LN.variable * sort
    | APP of LN.operator * abs spine ann
    | META_APP of (metavariable * sort) * (LN.symbol * sort) spine * abt spine ann
  and abs = ABS of (string * sort) spine * (string * sort) spine * abt

  val rec primToString =
    fn V (v, _) => LN.toString Variable.toString v
     | APP (theta, es <: _) =>
         Operator.toString (LN.toString Symbol.toString) theta
           ^ "("
           ^ Spine.pretty primToStringAbs ";" es
           ^ ")"
     | META_APP _ => "meta"
  and primToStringAbs =
    fn ABS (upsilon, gamma, m) =>
      (if Spine.isEmpty upsilon then "" else "{" ^ Spine.pretty (Sort.toString o #2) "," upsilon ^ "}")
      ^ (if Spine.isEmpty upsilon then "" else "[" ^ Spine.pretty (Sort.toString o #2) "," gamma ^ "]")
      ^ "." ^ primToString m

  type metaenv = abs MetaCtx.dict
  type varenv = abt VarCtx.dict
  type symenv = symbol SymCtx.dict

  fun abtToAbs m =
    ABS (Spine.empty (), Spine.empty (), m)

  (* Patterns for abstract binding trees. *)
  datatype 'a view =
      ` of variable
    | $ of operator * 'a bview spine
    | $# of metavariable * ((symbol * sort) spine * 'a spine)
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

  val sort =
    fn V (_, tau) => tau
     | APP (theta, _) => #2 (Operator.arity theta)
     | META_APP ((_, tau), _, _) => tau

  val metactx =
    fn V _ => MetaCtx.empty
     | APP (theta, es <: (mctx, _, _)) => mctx
     | META_APP ((mv, tau), us, ms <: (mctx, _, _)) =>
         let
           val vl = ((Spine.map #2 us, Spine.map sort ms), tau)
         in
           Ctx.MetaCtxUtil.extend mctx (mv, vl)
         end

  val symctx =
    fn V _ => SymCtx.empty
     | APP (theta, es <: (_, sctx, _)) =>
         List.foldr
           (fn ((LN.FREE u, tau), memo) => Ctx.SymCtxUtil.extend memo (u, tau)
             | (_, memo) => memo)
           sctx
           (Operator.support theta)
     | META_APP (_, us, ms <: (_, sctx, _)) =>
         Spine.foldr
           (fn ((LN.FREE u, tau), memo) => Ctx.SymCtxUtil.extend memo (u, tau)
             | (_, memo) => memo)
           sctx
           us

  val varctx =
    fn V (LN.FREE x, sigma) => VarCtx.singleton x sigma
     | V _ => VarCtx.empty
     | APP (theta, es <: (_, _, vctx)) => vctx
     | META_APP (_, _, ms <: (_, _, vctx)) => vctx

  fun getCtx m =
    (metactx m, symctx m, varctx m)

  fun mapAbs_ f (ABS (us, xs, m)) =
    ABS (us, xs, f m)

  fun liftTraverseAbs f coord =
    mapAbs_ (f (Coord.shiftRight coord))

  fun annotateApp theta es =
    let
      val ctx = Spine.foldr (fn (ABS (_, _, m), ctx) => Ctx.merge (ctx, getCtx m)) Ctx.empty es
    in
      APP (theta, es <: ctx)
    end

  fun annotateMetaApp (mv, tau) us ms =
    let
      val ctx = Spine.foldr (fn (m, ctx) => Ctx.merge (ctx, getCtx m)) Ctx.empty ms
    in
      META_APP ((mv, tau), us, ms <: ctx)
    end


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
     | APP (theta, es <: ctx) =>
         annotateApp theta (Spine.map (liftTraverseAbs (imprisonVariable (v, tau)) coord) es)
     | META_APP ((x, tau), us, ms <: ctx) =>
         annotateMetaApp (x, tau) us (Spine.map (imprisonVariable (v, tau) coord) ms)

  fun imprisonSymbol (v, tau) coord =
    fn V v => V v
     | APP (theta, es <: ctx) =>
         let
           fun rho v' = if Symbol.eq (v, v') then LN.BOUND coord else LN.FREE v'
           fun chk (LN.FREE v', tau') = if Symbol.eq (v, v') then assertSortEq (tau, tau') else ()
             | chk _ = ()
           val _ = List.app chk (Operator.support theta)
           val theta' = Operator.map (LN.bind rho) theta
           val ctx' = Ctx.modifySyms (fn sctx => SymCtx.remove sctx v) ctx
         in
           APP (theta', Spine.map (liftTraverseAbs (imprisonSymbol (v,tau)) coord) es <: ctx')
         end
     | META_APP (m, us, Ms <: ctx) =>
         let
           fun rho v' = if Symbol.eq (v, v') then LN.BOUND coord else LN.FREE v'
           fun rho' (l, s) = (LN.bind rho l, s)
           val vs = Spine.map rho' us
           val ctx' = Ctx.modifySyms (fn sctx => SymCtx.remove sctx v) ctx
         in
           META_APP (m, vs, Spine.map (imprisonSymbol (v, tau) coord) Ms <: ctx')
         end

  (* This is the reverse of the above, given a position we hunt around for
   * a bound variable in the correct slot and switch out for a free one.
   *)
  fun liberateVariable (v, sigma) coord =
    fn e as V (LN.FREE _, _) => e
     | e as V (LN.BOUND coord', sigma) =>
         if Coord.eq (coord, coord') then V (LN.FREE v, sigma) else e
     | APP (theta, es <: ctx) =>
         annotateApp theta (Spine.map (liftTraverseAbs (liberateVariable (v, sigma)) coord) es)
     | META_APP ((x, tau), us, ms <: ctx) =>
         annotateMetaApp (x, tau) us (Spine.map (liberateVariable (v, sigma) coord) ms)

  fun liberateSymbol (u, sigma) coord =
    let
      fun rho (LN.BOUND coord') = if Coord.eq (coord, coord') then LN.FREE u else LN.BOUND coord'
        | rho u' = u'
    in
      fn e as V _ => e
       | APP (theta, es <: ctx) =>
           let
             val theta' = Operator.map rho theta
             val fs = Spine.map (liftTraverseAbs (liberateSymbol (u, sigma)) coord) es
           in
             annotateApp theta' fs
           end
       | META_APP ((x, tau), us, ms <: ctx) =>
           let
             val vs = Spine.map (fn (l,s) => (rho l, s)) us
             val ns = Spine.map (liberateSymbol (u, sigma) coord) ms
             val ctx' = Ctx.modifySyms (fn sctx => SymCtx.insert sctx u sigma) ctx
           in
             annotateMetaApp (x, tau) vs ns
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

    val liberateVariables : (variable * sort) Spine.t -> abt -> abt =
      foldStar liberateVariable

    val liberateSymbols : (symbol * sort) Spine.t -> abt -> abt =
      foldStar liberateSymbol
  end


  fun checkb ((us, xs) \ m, ((ssorts, vsorts), sigma)) =
    let
      val (_, tau) = infer m
      val () = assertSortEq (sigma, tau)
    in
      ABS
        (Spine.Pair.zipEq (Spine.map Symbol.toString us, ssorts),
         Spine.Pair.zipEq (Spine.map Variable.toString xs, vsorts),
         imprisonSymbols (us, ssorts) (imprisonVariables (xs, vsorts) m))
    end

  and infer M =
    case M of
         V (x, tau) => (` (LN.getFree x), tau)
       | APP (theta, Es <: _) =>
         let
           val (_, tau) = Operator.arity theta
           val theta' = Operator.map LN.getFree theta
           val Es' = Spine.map (#1 o inferb) Es
         in
           (theta' $ Es', tau)
         end
       | META_APP ((mv, tau), us, Ms <: _) =>
         let
           val us' = Spine.map (fn (u, sigma) => (LN.getFree u, sigma)) us
         in
           (mv $# (us', Ms), tau)
         end

  and inferb (ABS (upsilon, gamma, m)) =
    let
      val us = Spine.map (fn (u, tau) => (Symbol.named u, tau)) upsilon
      val xs = Spine.map (fn (x, tau) => (Variable.named x, tau)) gamma
      val m' = liberateSymbols us (liberateVariables xs m)
      val (_, tau) = infer m'
      val valence = ((Spine.map #2 upsilon, Spine.map #2 gamma), tau)
    in
      ((Spine.map #1 us, Spine.map #1 xs) \ m',
       valence)
    end

  val out = #1 o infer
  val outb = #1 o inferb
  val valence = #2 o inferb

  fun check (m, sigma) =
    case m of
         `x => V (LN.FREE x, sigma)
       | theta $ es =>
           let
             val (valences, tau)  = Operator.arity theta
             val () = assertSortEq (sigma, tau)
             val theta' = Operator.map LN.FREE theta
             val es' = Spine.Pair.mapEq checkb (es, valences)
           in
             annotateApp theta' es'
           end
       | x $# (us, ms) =>
           let
             val ssorts = Spine.map #2 us
             val vsorts = Spine.map sort ms

             val us' = Spine.map (fn (u, tau) => (LN.FREE u, tau)) us
             fun chkInf (m, tau) =
               (assertSortEq (tau, sort m); m)
             val ms' = Spine.Pair.mapEq chkInf (ms, vsorts)
             val ctx = Spine.foldr (fn (m, ctx) => Ctx.merge (ctx, getCtx m)) Ctx.empty ms'
           in
             annotateMetaApp (x, sigma) us' ms'
           end


  fun mapb f ((us, xs) \ m) =
    (us, xs) \ f m

  fun mapAbs f abs =
    let
      val ((us, xs) \ m, vl) = inferb abs
    in
      checkb ((us, xs) \ f m, vl)
    end

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
      | eq (APP (theta, es <: _), APP (theta', es' <: _)) =
          OpLnEq.eq (theta, theta') andalso Spine.Pair.allEq eqAbs (es, es')
      | eq (META_APP ((mv, _), us, ms <: _), META_APP ((mv', _), us', ms' <: _)) =
          Metavariable.eq (mv, mv')
            andalso Spine.Pair.allEq (fn ((x, _), (y, _)) => LN.eq Symbol.eq (x,y)) (us, us')
            andalso Spine.Pair.allEq eq (ms, ms')
      | eq _ = false
    and eqAbs (ABS (_, _, m), ABS (_, _, m')) = eq (m, m')
  end

  fun metasubstEnv rho m =
    let
      val (view, tau) = infer m
    in
      case view of
           `x => m
         | theta $ es =>
             check (theta $ Spine.map (mapb (metasubstEnv rho)) es, tau)
         | mv $# (us, ms) =>
             let
               val ms' = Spine.map (metasubstEnv rho) ms
             in
               case MetaCtx.find rho mv of
                    NONE =>
                      check (mv $# (us, ms'), tau)
                  | SOME abs =>
                      let
                        val (vs, xs) \ m = outb abs
                        val srho =
                          Spine.foldr
                            (fn (((u, _), v), r) => SymCtx.insert r u v)
                            SymCtx.empty
                            (Spine.Pair.zipEq (us, vs))
                        val rho' =
                          Spine.foldr
                            (fn ((x,m), rho) => VarCtx.insert rho x m)
                            VarCtx.empty
                            (Spine.Pair.zipEq (xs, ms'))
                      in
                        substEnv rho' (renameEnv srho m)
                      end
             end
    end

  and substEnv rho =
    fn m as V (LN.FREE x, sigma) => getOpt (VarCtx.find rho x, m)
     | m as V _ => m
     | APP (theta, es <: _) => annotateApp theta (Spine.map (mapAbs_ (substEnv rho)) es)
     | META_APP ((x, tau), us, ms <: _) => annotateMetaApp (x, tau) us (Spine.map (substEnv rho) ms)

  and renameEnv rho =
    fn m as V _ => m
     | APP (theta, es <: _) =>
         let
           fun ren u = getOpt (SymCtx.find rho u, u)
           val theta' = Operator.map (LN.map ren) theta
         in
           annotateApp theta' (Spine.map (mapAbs_ (renameEnv rho)) es)
         end
     | META_APP ((x, tau), us, ms <: _) =>
         let
           fun ren u = getOpt (SymCtx.find rho u, u)
           fun ren' (l,s) = (LN.map ren l, s)
         in
           annotateMetaApp (x, tau) (Spine.map ren' us) (Spine.map (renameEnv rho) ms)
         end

  fun unbind abs us ms =
    let
      val (vs, xs) \ m = outb abs
      val srho =
        Spine.foldr
          (fn ((v,u), rho) => SymCtx.insert rho v u)
          SymCtx.empty
          (Spine.Pair.zipEq (vs, us))
      val vrho =
        Spine.foldr
          (fn ((x,m), rho) => VarCtx.insert rho x m)
          VarCtx.empty
          (Spine.Pair.zipEq (xs, ms))
    in
      substEnv vrho (renameEnv srho m)
    end

  fun // (abs, (us, ms)) =
    unbind abs us ms


  fun subst (n, x) = substEnv (VarCtx.insert VarCtx.empty x n)
  fun metasubst (e, mv) = metasubstEnv (MetaCtx.insert MetaCtx.empty mv e)
  fun rename (v, u) = renameEnv (SymCtx.insert SymCtx.empty u v)

  fun mapSubterms f m =
    let
      val (view, tau) = infer m
    in
      check (map f view, tau)
    end

  fun deepMapSubterms f m =
    mapSubterms (f o deepMapSubterms f) m

  structure Unify =
  struct
    type renaming = metavariable MetaCtx.dict * symbol SymCtx.dict * variable VarCtx.dict

    exception UnificationFailed

    structure MetaRenUtil = ContextUtil (structure Ctx = MetaCtx and Elem = Metavariable)
    structure SymRenUtil = ContextUtil (structure Ctx = SymCtx and Elem = Symbol)
    structure VarRenUtil = ContextUtil (structure Ctx = VarCtx and Elem = Variable)

    fun unifySymbols ((u, sigma), (v, tau), rho) =
      if Sort.eq (sigma, tau) then
        case (u, v) of
            (LN.FREE u', LN.FREE v') =>
              SymRenUtil.extend rho (u', v')
          | (LN.BOUND i, LN.BOUND j) =>
              if Coord.eq (i, j) then
                rho
              else
                raise UnificationFailed
          | _ => raise UnificationFailed
      else
        raise UnificationFailed

    fun unifyOperator rho (theta1 : LN.operator, theta2 : LN.operator) : symbol SymCtx.dict =
      if Operator.eq (fn _ => true) (theta1, theta2) then
        let
          val us = Operator.support theta1
          val vs = Operator.support theta2
        in
          ListPair.foldlEq unifySymbols rho (us, vs)
        end
      else
        raise UnificationFailed

    local
      fun go (mrho, srho, vrho) =
        fn (V (LN.FREE x, sigma), V (LN.FREE y, tau)) =>
             if Sort.eq (sigma, tau) then
               (mrho, srho, VarRenUtil.extend vrho (x, y))
             else
               raise UnificationFailed
         | (V (LN.BOUND i, _), V (LN.BOUND j, _)) =>
             if Coord.eq (i, j) then
               (mrho, srho, vrho)
             else
               raise UnificationFailed
         | (APP (theta1, es1 <: _), APP (theta2, es2 <: _)) =>
             let
               val srho' = unifyOperator srho (theta1, theta2)
             in
               Spine.foldr
                 (fn ((ABS (_, _, m1), ABS (_, _, m2)), acc) => go acc (m1, m2))
                 (mrho, srho', vrho)
                 (Spine.Pair.zipEq (es1, es2))
             end
         | (META_APP ((x1, tau1), us1, ms1 <: _), META_APP ((x2, tau2), us2, ms2 <: _)) =>
             let
               val _ = if Sort.eq (tau1, tau2) then () else raise UnificationFailed
               val mrho' =
                 MetaRenUtil.extend mrho (x1, x2)
               val srho' =
                 Spine.foldr
                   (fn ((u, v), rho) => unifySymbols (u, v, rho))
                   srho
                   (Spine.Pair.zipEq (us1, us2))
             in
               Spine.foldr
                 (fn ((m1, m2), acc) => go acc (m1, m2))
                 (mrho', srho', vrho)
                 (Spine.Pair.zipEq (ms1, ms2))
             end
         | _ => raise UnificationFailed
    in
      fun unify (m,n) =
        go (MetaCtx.empty, SymCtx.empty, VarCtx.empty) (m,n)
        handle MetaRenUtil.MergeFailure => raise UnificationFailed
             | SymRenUtil.MergeFailure => raise UnificationFailed
             | VarRenUtil.MergeFailure => raise UnificationFailed
             | e => raise e
    end

    fun unifyOpt (m, n) =
      SOME (unify (m, n))
      handle UnificationFailed => NONE
  end

end

functor SimpleAbt (Operator : OPERATOR) =
  Abt (structure Symbol = Symbol ()
       structure Variable = Symbol ()
       structure Metavariable = Symbol ()
       structure Operator = Operator)
