functor Abt
  (structure Sym : ABT_SYMBOL
   structure Var : ABT_SYMBOL
   structure Metavar : ABT_SYMBOL
   structure O : ABT_OPERATOR
   structure P : ABT_PARAM) : ABT =
struct
  structure Sym = Sym and Var = Var and Metavar = Metavar and O = O and Ar = O.Ar
  structure S = Ar.Vl.S and Valence = Ar.Vl
  structure Sp = Valence.Sp

  structure P =
  struct
    structure F = FunctorOfMonad (P)
    open P F
  end

  structure MetaCtx = Metavar.Ctx
  structure VarCtx = Var.Ctx
  structure SymCtx = Sym.Ctx

  type sort = S.t
  type valence = Valence.t
  type coord = LnCoord.t
  type symbol = Sym.t
  type variable = Var.t
  type metavariable = Metavar.t
  type 'a spine = 'a Sp.t
  type 'a param = 'a P.t
  type operator = symbol param O.t

  structure LN =
  struct
    local structure S = LocallyNameless (LnCoord) in open S end
    type symbol = symbol t
    type param = symbol param
    type operator = param O.t
    type variable = variable t
  end

  type metactx = valence MetaCtx.dict
  type varctx = sort VarCtx.dict
  type symctx = sort SymCtx.dict

  structure Ctx =
  struct
    structure MetaCtxUtil = ContextUtil (structure Ctx = MetaCtx and Elem = Valence)
    structure VarCtxUtil = ContextUtil (structure Ctx = VarCtx and Elem = S)
    structure SymCtxUtil = ContextUtil (structure Ctx = SymCtx and Elem = S)

    type ctx = metactx Susp.susp * symctx Susp.susp * varctx Susp.susp

    val empty : ctx =
      (Susp.delay (fn _ => MetaCtx.empty),
       Susp.delay (fn _ => SymCtx.empty),
       Susp.delay (fn _ => VarCtx.empty))

    fun merge ((mctx1, sctx1, vctx1), (mctx2, sctx2, vctx2)) =
      let
        val mctx = Susp.delay (fn _ => MetaCtxUtil.union (Susp.force mctx1, Susp.force mctx2))
        val sctx = Susp.delay (fn _ => SymCtxUtil.union (Susp.force sctx1, Susp.force sctx2))
        val vctx = Susp.delay (fn _ => VarCtxUtil.union (Susp.force vctx1, Susp.force vctx2))
      in
        (mctx, sctx, vctx)
      end

    fun modifyMetas f (mctx, sctx, vctx) =
      (Susp.delay (fn _ => f (Susp.force mctx)), sctx, vctx)

    fun modifySyms f (mctx, sctx, vctx) =
      (mctx, Susp.delay (fn _ => f (Susp.force sctx)), vctx)

    fun modifyVars f (mctx, sctx, vctx) =
      (mctx, sctx, Susp.delay (fn _ => f (Susp.force vctx)))
  end

  datatype 'a ann = <: of 'a * Ctx.ctx
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
    | META_APP of (metavariable * sort) * (LN.param * sort) spine * abt spine ann
  and abs = ABS of (string * sort) spine * (string * sort) spine * abt

  val rec primToString =
    fn V (v, _) => LN.toString Var.toString v
     | APP (theta, es <: _) =>
         O.toString (P.toString (LN.toString Sym.toString)) theta
           ^ "("
           ^ Sp.pretty primToStringAbs ";" es
           ^ ")"
     | META_APP _ => "meta"
  and primToStringAbs =
    fn ABS (upsilon, gamma, m) =>
      (if Sp.isEmpty upsilon then "" else "{" ^ Sp.pretty (S.toString o #2) "," upsilon ^ "}")
      ^ (if Sp.isEmpty upsilon then "" else "[" ^ Sp.pretty (S.toString o #2) "," gamma ^ "]")
      ^ "." ^ primToString m

  type metaenv = abs MetaCtx.dict
  type varenv = abt VarCtx.dict
  type symenv = symbol param SymCtx.dict

  fun abtToAbs m =
    ABS (Sp.empty (), Sp.empty (), m)

  (* Patterns for abstract binding trees. *)
  datatype 'a view =
      ` of variable
    | $ of operator * 'a bview spine
    | $# of metavariable * ((symbol param * sort) spine * 'a spine)
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
      ("expected " ^ S.toString sigma ^ " == " ^ S.toString tau)
      (S.eq (sigma, tau))

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
     | APP (theta, _) => #2 (O.arity theta)
     | META_APP ((_, tau), _, _) => tau

  val metactx =
    fn V _ => MetaCtx.empty
     | APP (theta, es <: (mctx, _, _)) => Susp.force mctx
     | META_APP ((mv, tau), ps, ms <: (mctx, _, _)) =>
         let
           val vl = ((Sp.map #2 ps, Sp.map sort ms), tau)
         in
           Ctx.MetaCtxUtil.extend (Susp.force mctx) (mv, vl)
         end

  val symctx =
    fn V _ => SymCtx.empty
     | APP (theta, es <: (_, sctx, _)) =>
         List.foldr
           (fn ((p, tau), memo) =>
              (case P.extract p of
                  SOME (LN.FREE u) => Ctx.SymCtxUtil.extend memo (u, tau)
                | _ => memo))
           (Susp.force sctx)
           (O.support theta)
     | META_APP (_, ps, ms <: (_, sctx, _)) =>
         Sp.foldr
           (fn ((p, tau), memo) =>
              (case P.extract p of
                  SOME (LN.FREE u) => Ctx.SymCtxUtil.extend memo (u, tau)
                | _ => memo))
           (Susp.force sctx)
           ps

  val varctx =
    fn V (LN.FREE x, sigma) => VarCtx.singleton x sigma
     | V _ => VarCtx.empty
     | APP (theta, es <: (_, _, vctx)) => Susp.force vctx
     | META_APP (_, _, ms <: (_, _, vctx)) => Susp.force vctx

  fun getCtx m : Ctx.ctx =
    (Susp.delay (fn _ => metactx m),
     Susp.delay (fn _ => symctx m),
     Susp.delay (fn _ => varctx m))

  fun mapAbs_ f (ABS (us, xs, m)) =
    ABS (us, xs, f m)

  fun liftTraverseAbs f coord =
    mapAbs_ (f (LnCoord.shiftRight coord))

  fun annotateApp theta es =
    let
      val ctx = Sp.foldr (fn (ABS (_, _, m), ctx) => Ctx.merge (ctx, getCtx m)) Ctx.empty es
    in
      APP (theta, es <: ctx)
    end

  fun annotateMetaApp (mv, tau) us ms =
    let
      val ctx = Sp.foldr (fn (m, ctx) => Ctx.merge (ctx, getCtx m)) Ctx.empty ms
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
         if Var.eq (v, v') then
           (assertSortEq (sigma, tau);
            V (LN.BOUND coord, sigma))
         else
           m
     | V v => V v
     | APP (theta, es <: ctx) =>
         annotateApp theta (Sp.map (liftTraverseAbs (imprisonVariable (v, tau)) coord) es)
     | META_APP (mv, us, ms <: ctx) =>
         annotateMetaApp mv us (Sp.map (imprisonVariable (v, tau) coord) ms)

  fun imprisonSymbol (v, tau) coord =
    fn V v => V v
     | APP (theta, es <: ctx) =>
         let
           fun rho v' = if Sym.eq (v, v') then LN.BOUND coord else LN.FREE v'
           fun chk (p', tau') =
             case P.extract p' of
                SOME (LN.FREE v') => if Sym.eq (v, v') then assertSortEq (tau, tau') else ()
              | _ => ()
           val _ = List.app chk (O.support theta)
           val theta' = O.map (P.map (LN.bind rho)) theta
           val ctx' = Ctx.modifySyms (fn sctx => SymCtx.remove sctx v) ctx
         in
           APP (theta', Sp.map (liftTraverseAbs (imprisonSymbol (v,tau)) coord) es <: ctx')
         end
     | META_APP (m, ps, Ms <: ctx) =>
         let
           fun rho v' = if Sym.eq (v, v') then LN.BOUND coord else LN.FREE v'
           fun rho' (l, s) = (P.map (LN.bind rho) l, s)
           val vs = Sp.map rho' ps
           val ctx' = Ctx.modifySyms (fn sctx => SymCtx.remove sctx v) ctx
         in
           META_APP (m, vs, Sp.map (imprisonSymbol (v, tau) coord) Ms <: ctx')
         end

  (* This is the reverse of the above, given a position we hunt around for
   * a bound variable in the correct slot and switch out for a free one.
   *)
  fun liberateVariable (v, sigma) coord =
    fn e as V (LN.FREE _, _) => e
     | e as V (LN.BOUND coord', sigma) =>
         if LnCoord.eq (coord, coord') then V (LN.FREE v, sigma) else e
     | APP (theta, es <: ctx) =>
         annotateApp theta (Sp.map (liftTraverseAbs (liberateVariable (v, sigma)) coord) es)
     | META_APP ((x, tau), ps, ms <: ctx) =>
         annotateMetaApp (x, tau) ps (Sp.map (liberateVariable (v, sigma) coord) ms)

  fun liberateSymbol (u, sigma) coord =
    let
      fun rho (LN.BOUND coord') = if LnCoord.eq (coord, coord') then LN.FREE u else LN.BOUND coord'
        | rho u' = u'
    in
      fn e as V _ => e
       | APP (theta, es <: ctx) =>
           let
             val theta' = O.map (P.map rho) theta
             val fs = Sp.map (liftTraverseAbs (liberateSymbol (u, sigma)) coord) es
           in
             annotateApp theta' fs
           end
       | META_APP ((x, tau), ps, ms <: ctx) =>
           let
             val qs = Sp.map (fn (l,s) => (P.map rho l, s)) ps
             val ns = Sp.map (liberateSymbol (u, sigma) coord) ms
             val ctx' = Ctx.modifySyms (fn sctx => SymCtx.insert sctx u sigma) ctx
           in
             annotateMetaApp (x, tau) qs ns
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
      fun comp (f, g) (coord, a) = f (coord, g (LnCoord.shiftDown coord, a))
    end

    structure ShiftFoldMap =
      CategoryFoldMap
        (structure C = ShiftFunCat
         structure F = Sp)

    fun foldStar f xs t =
      ShiftFoldMap.foldMap
        (fn v => fn (c, M) => f v c M)
        xs
        (LnCoord.origin, t)
  in
    val imprisonVariables = foldStar imprisonVariable o Sp.Pair.zipEq
    val imprisonSymbols = foldStar imprisonSymbol o Sp.Pair.zipEq

    val liberateVariables : (variable * sort) Sp.t -> abt -> abt =
      foldStar liberateVariable

    val liberateSymbols : (symbol * sort) Sp.t -> abt -> abt =
      foldStar liberateSymbol
  end


  fun checkb ((us, xs) \ m, ((psorts, vsorts), sigma)) =
    let
      val (_, tau) = infer m
      val () = assertSortEq (sigma, tau)
    in
      ABS
        (Sp.Pair.zipEq (Sp.map Sym.toString us, psorts),
         Sp.Pair.zipEq (Sp.map Var.toString xs, vsorts),
         imprisonSymbols (us, psorts) (imprisonVariables (xs, vsorts) m))
    end

  and infer M =
    case M of
         V (x, tau) => (` (LN.getFree x), tau)
       | APP (theta, Es <: _) =>
         let
           val (_, tau) = O.arity theta
           val theta' = O.map (P.map LN.getFree) theta
           val Es' = Sp.map (#1 o inferb) Es
         in
           (theta' $ Es', tau)
         end
       | META_APP ((mv, tau), ps, Ms <: _) =>
         let
           val ps' = Sp.map (fn (p, sigma) => (P.map (LN.getFree) p, sigma)) ps
         in
           (mv $# (ps', Ms), tau)
         end

  and inferb (ABS (upsilon, gamma, m)) =
    let
      val syms = symctx m
      val vars = varctx m

      val us = Sp.map (fn (u, tau) => (Sym.fresh syms u, tau)) upsilon
      val xs = Sp.map (fn (x, tau) => (Var.fresh vars x, tau)) gamma
      val m' = liberateSymbols us (liberateVariables xs m)
      val (_, tau) = infer m'
      val valence = ((Sp.map #2 upsilon, Sp.map #2 gamma), tau)
    in
      ((Sp.map #1 us, Sp.map #1 xs) \ m',
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
             val (valences, tau)  = O.arity theta
             val () = assertSortEq (sigma, tau)
             val theta' = O.map (P.map LN.FREE) theta
             val es' = Sp.Pair.mapEq checkb (es, valences)
           in
             annotateApp theta' es'
           end
       | x $# (ps, ms) =>
           let
             val psorts = Sp.map #2 ps
             val vsorts = Sp.map sort ms

             val ps' = Sp.map (fn (p, tau) => (P.map LN.FREE p, tau)) ps
             fun chkInf (m, tau) = (assertSortEq (tau, sort m); m)
             val ms' = Sp.Pair.mapEq chkInf (ms, vsorts)
             val ctx = Sp.foldr (fn (m, ctx) => Ctx.merge (ctx, getCtx m)) Ctx.empty ms'
           in
             annotateMetaApp (x, sigma) ps' ms'
           end

  fun $$ (theta, es) =
    let
      val (_, tau) = O.arity theta
    in
      check (theta $ es, tau)
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
         theta $ Sp.map (mapb f) es
     | mv $# (us, ms) =>
         mv $# (us, Sp.map f ms)

  local
    structure OpLnEq = struct val eq = O.eq (P.eq (LN.eq Sym.eq)) end
  in
    (* While this looks simple by using locally nameless representations this
     * implements alpha equivalence (and is very efficient!)
     *)
    fun eq (V (v, _), V (v', _)) = LN.eq Var.eq (v, v')
      | eq (APP (theta, es <: _), APP (theta', es' <: _)) =
          OpLnEq.eq (theta, theta') andalso Sp.Pair.allEq eqAbs (es, es')
      | eq (META_APP ((mv, _), ps, ms <: _), META_APP ((mv', _), ps', ms' <: _)) =
          Metavar.eq (mv, mv')
            andalso Sp.Pair.allEq (fn ((p, _), (q, _)) => P.eq (LN.eq Sym.eq) (p,q)) (ps, ps')
            andalso Sp.Pair.allEq eq (ms, ms')
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
             check (theta $ Sp.map (mapb (metasubstEnv rho)) es, tau)
         | mv $# (ps, ms) =>
             let
               val ms' = Sp.map (metasubstEnv rho) ms
             in
               case MetaCtx.find rho mv of
                    NONE =>
                      check (mv $# (ps, ms'), tau)
                  | SOME abs =>
                      let
                        val (vs, xs) \ m = outb abs
                        val srho =
                          Sp.foldr
                            (fn ((v, (p, _)), r) => SymCtx.insert r v p)
                            SymCtx.empty
                            (Sp.Pair.zipEq (vs, ps))
                        val rho' =
                          Sp.foldr
                            (fn ((x,m), rho) => VarCtx.insert rho x m)
                            VarCtx.empty
                            (Sp.Pair.zipEq (xs, ms'))
                      in
                        substEnv rho' (renameEnv srho m)
                      end
             end
    end

  and substEnv rho =
    fn m as V (LN.FREE x, sigma) => getOpt (VarCtx.find rho x, m)
     | m as V _ => m
     | APP (theta, es <: _) => annotateApp theta (Sp.map (mapAbs_ (substEnv rho)) es)
     | META_APP (mv, us, ms <: _) => annotateMetaApp mv us (Sp.map (substEnv rho) ms)

  and renameEnv rho =
    fn m as V _ => m
     | APP (theta, es <: _) =>
         let
           fun ren (LN.FREE u) = P.map LN.FREE (getOpt (SymCtx.find rho u, P.pure u))
             | ren l = P.pure l
           val theta' = O.map (P.bind ren) theta
         in
           annotateApp theta' (Sp.map (mapAbs_ (renameEnv rho)) es)
         end
     | META_APP (mv, us, ms <: _) =>
         let
           fun ren (LN.FREE u) = P.map LN.FREE (getOpt (SymCtx.find rho u, P.pure u))
             | ren l = P.pure l
           fun ren' (l,s) = (P.bind ren l, s)
         in
           annotateMetaApp mv (Sp.map ren' us) (Sp.map (renameEnv rho) ms)
         end

  fun unbind abs us ms =
    let
      val (vs, xs) \ m = outb abs
      val srho =
        Sp.foldr
          (fn ((v,u), rho) => SymCtx.insert rho v (P.pure u))
          SymCtx.empty
          (Sp.Pair.zipEq (vs, us))
      val vrho =
        Sp.foldr
          (fn ((x,m), rho) => VarCtx.insert rho x m)
          VarCtx.empty
          (Sp.Pair.zipEq (xs, ms))
    in
      substEnv vrho (renameEnv srho m)
    end

  fun // (abs, (us, ms)) =
    unbind abs us ms


  fun subst (n, x) = substEnv (VarCtx.insert VarCtx.empty x n)
  fun metasubst (e, mv) = metasubstEnv (MetaCtx.insert MetaCtx.empty mv e)
  fun rename (p, u) = renameEnv (SymCtx.insert SymCtx.empty u p)

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

    structure MetaRenUtil = ContextUtil (structure Ctx = MetaCtx and Elem = Metavar)
    structure SymRenUtil = ContextUtil (structure Ctx = SymCtx and Elem = Sym)
    structure VarRenUtil = ContextUtil (structure Ctx = VarCtx and Elem = Var)

    fun unifyParams ((p, sigma), (q, tau), rho) =
      if S.eq (sigma, tau) then
        case (P.extract p, P.extract q) of
           (SOME (LN.FREE u'), SOME (LN.FREE v')) =>
              SymRenUtil.extend rho (u', v')
         | (SOME (LN.BOUND i), SOME (LN.BOUND j)) =>
              if LnCoord.eq (i, j) then
                rho
              else
                raise UnificationFailed
         | _ =>
              if P.eq (LN.eq Sym.eq) (p, q) then
                rho
              else
                 raise UnificationFailed
      else
        raise UnificationFailed

    fun unifyOperator rho (theta1 : LN.operator, theta2 : LN.operator) : symbol SymCtx.dict =
      if O.eq (fn _ => true) (theta1, theta2) then
        let
          val us = O.support theta1
          val vs = O.support theta2
        in
          ListPair.foldlEq unifyParams rho (us, vs)
        end
      else
        raise UnificationFailed

    local
      fun go (mrho, srho, vrho) =
        fn (V (LN.FREE x, sigma), V (LN.FREE y, tau)) =>
             if S.eq (sigma, tau) then
               (mrho, srho, VarRenUtil.extend vrho (x, y))
             else
               raise UnificationFailed
         | (V (LN.BOUND i, _), V (LN.BOUND j, _)) =>
             if LnCoord.eq (i, j) then
               (mrho, srho, vrho)
             else
               raise UnificationFailed
         | (APP (theta1, es1 <: _), APP (theta2, es2 <: _)) =>
             let
               val srho' = unifyOperator srho (theta1, theta2)
             in
               Sp.foldr
                 (fn ((ABS (_, _, m1), ABS (_, _, m2)), acc) => go acc (m1, m2))
                 (mrho, srho', vrho)
                 (Sp.Pair.zipEq (es1, es2))
             end
         | (META_APP ((x1, tau1), ps1, ms1 <: _), META_APP ((x2, tau2), ps2, ms2 <: _)) =>
             let
               val _ = if S.eq (tau1, tau2) then () else raise UnificationFailed
               val mrho' =
                 MetaRenUtil.extend mrho (x1, x2)
               val srho' =
                 Sp.foldr
                   (fn ((p, q), rho) => unifyParams (p, q, rho))
                   srho
                   (Sp.Pair.zipEq (ps1, ps2))
             in
               Sp.foldr
                 (fn ((m1, m2), acc) => go acc (m1, m2))
                 (mrho', srho', vrho)
                 (Sp.Pair.zipEq (ms1, ms2))
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

structure IdMonad =
struct
  type 'i t = 'i
  fun pure x = x
  fun bind f x = f x

  fun extract x = SOME x
  fun eq f = f
  fun toString f = f
end

structure CubeMonad =
struct
  datatype 'i t =
     NAME of 'i
   | DIM0
   | DIM1

  val pure = NAME

  fun bind f =
    fn NAME u => f u
     | DIM0 => DIM0
     | DIM1 => DIM1

  val extract =
    fn NAME u => SOME u
     | _ => NONE

  fun eq f =
    fn (NAME u, NAME v) => f (u, v)
     | (DIM0, DIM0) => true
     | (DIM1, DIM1) => true
     | _ => false

  fun toString f =
    fn NAME u => f u
     | DIM0 => "dim0"
     | DIM1 => "dim1"
end

functor SimpleAbt (O : ABT_OPERATOR) =
  Abt (structure Sym = AbtSymbol ()
       structure Var = AbtSymbol ()
       structure Metavar = AbtSymbol ()
       structure O = O
       structure P = IdMonad)

functor CubicalAbt (O : ABT_OPERATOR) =
  Abt (structure Sym = AbtSymbol ()
       structure Var = AbtSymbol ()
       structure Metavar = AbtSymbol ()
       structure O = O
       structure P = CubeMonad)
