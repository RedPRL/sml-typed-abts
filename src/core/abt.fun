functor Abt
  (structure Sym : ABT_SYMBOL
   structure Var : ABT_SYMBOL
   structure Metavar : ABT_SYMBOL
   structure O : ABT_OPERATOR
   type annotation) : ABT =
struct
  structure Sym = Sym and Var = Var and Metavar = Metavar and O = O and Ar = O.Ar
  structure S = Ar.Vl.S and PS = Ar.Vl.PS and Valence = Ar.Vl
  structure Sp = Valence.Sp
  structure P = O.P

  structure MetaCtx = Metavar.Ctx
  structure VarCtx = Var.Ctx
  structure SymCtx = Sym.Ctx

  type sort = S.t
  type psort = PS.t
  type valence = Valence.t
  type coord = LnCoord.t
  type symbol = Sym.t
  type variable = Var.t
  type metavariable = Metavar.t
  type operator = symbol O.t
  type param = symbol P.term
  type 'a spine = 'a Sp.t
  type annotation = annotation

  structure Views = AbtViews (Sp)
  open Views

  type 'a view = (param, psort, symbol, variable, metavariable, operator, 'a) termf
  type 'a bview = (symbol, variable, 'a) bindf
  type 'a appview = (symbol, variable, operator, 'a) appf

  infixr 5 \
  infix 5 $ $#


  structure LN =
  struct
    local structure S = LocallyNameless (LnCoord) in open S end
    type symbol = symbol t
    type operator = symbol O.t
    type variable = variable t
  end

  type metactx = valence MetaCtx.dict
  type varctx = sort VarCtx.dict
  type symctx = psort SymCtx.dict

  structure Ctx =
  struct
    structure MetaCtxUtil = ContextUtil (structure Ctx = MetaCtx and Elem = Valence)
    structure VarCtxUtil = ContextUtil (structure Ctx = VarCtx and Elem = S)
    structure SymCtxUtil = ContextUtil (structure Ctx = SymCtx and Elem = PS)

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

  datatype 'a ctx_ann = <: of 'a * Ctx.ctx
  infix <:

  datatype 'a ann = @: of 'a * annotation option
  infix @:

  structure Ann =
  struct
    fun map f (m @: ann) = f m @: ann
    fun unAnn (m @: _) = m
  end

  (* Note that we use LN.variable so V may work with both free and bound
   * variables and LN.operator/symbols to distinguish free and bound symbols.
   * Otherwise this is almost the same as a pattern except that
   * we annotate things with sorts/valences so that we can always determine sorts
   * without a context
   *)
  datatype abt_internal =
      V of LN.variable * sort
    | APP of LN.operator * abs spine ctx_ann
    | META_APP of (metavariable * sort) * (LN.symbol P.term * psort) spine * abt spine ctx_ann
  and abs = ABS of (string * psort) spine * (string * sort) spine * abt
  withtype abt = abt_internal ann

  fun annotate ann (m @: _) = m @: SOME ann
  fun getAnnotation (_ @: ann) = ann
  fun setAnnotation ann (m @: _) = m @: ann
  fun clearAnnotation (m @: _) = m @: NONE


  val rec primToString =
    fn V (v, _) @: _ => LN.toString Var.toString v
     | APP (theta, es <: _) @: _ =>
         O.toString (LN.toString Sym.toString) theta
           ^ "("
           ^ Sp.pretty primToStringAbs "; " es
           ^ ")"
     | META_APP ((x, tau), ps, ms <: _) @: _ =>
         "#" ^ Metavar.toString x 
           ^ "{" ^ Sp.pretty (P.toString (LN.toString Sym.toString) o #1) ", " ps ^ "}"
           ^ "[" ^ Sp.pretty primToString ", " ms ^ "]"
  and primToStringAbs =
    fn ABS (upsilon, gamma, m) =>
      "{" ^ Sp.pretty (PS.toString o #2) ", " upsilon ^ "}"
      ^ "[" ^ Sp.pretty (S.toString o #2) ", " gamma ^ "]"
      ^ "." ^ primToString m

  fun bindToString ((us, xs) \ m) = 
    "{" ^ Sp.pretty Sym.toString ", " us ^ "}"
      ^ "[" ^ Sp.pretty Var.toString ", " xs ^ "]."
      ^ primToString m
      

  type metaenv = abs MetaCtx.dict
  type varenv = abt VarCtx.dict
  type symenv = param SymCtx.dict

  fun abtToAbs m =
    ABS (Sp.empty (), Sp.empty (), m)

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

  fun assertPSortEq (sigma, tau) =
    assert
      ("expected " ^ PS.toString sigma ^ " == " ^ PS.toString tau)
      (PS.eq (sigma, tau))

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
    fn V (_, tau) @: _ => tau
     | APP (theta, _) @: _ => #2 (O.arity theta)
     | META_APP ((_, tau), _, _) @: _ => tau

  val metactx =
    fn V _ @: _ => MetaCtx.empty
     | APP (theta, es <: (mctx, _, _)) @: _ => Susp.force mctx
     | META_APP ((mv, tau), us, ms <: (mctx, _, _)) @: _ =>
         let
           val vl = ((Sp.map #2 us, Sp.map sort ms), tau)
         in
           Ctx.MetaCtxUtil.extend (Susp.force mctx) (mv, vl)
         end

  val symctx =
    fn V _ @: _ => SymCtx.empty
     | APP (theta, es <: (_, sctx, _)) @: _ =>
         List.foldr
           (fn ((LN.FREE u, tau), memo) => Ctx.SymCtxUtil.extend memo (u, tau)
             | (_, memo) => memo)
           (Susp.force sctx)
           (O.support theta)
     | META_APP (_, ps, ms <: (_, sctx, _)) @: _ =>
         Sp.foldr
           (fn ((P.VAR (LN.FREE u), tau), memo) => Ctx.SymCtxUtil.extend memo (u, tau)
             | ((P.APP t, tau), memo) =>
                 List.foldr
                   (fn ((LN.FREE u,sigma), memo') => Ctx.SymCtxUtil.extend memo' (u, sigma)
                     | (_, memo') => memo')
                   memo
                   (P.freeVars t)
             | (_, memo) => memo)
           (Susp.force sctx)
           ps

  val varctx =
    fn V (LN.FREE x, sigma) @: _ => VarCtx.singleton x sigma
     | V _ @: _ => VarCtx.empty
     | APP (theta, es <: (_, _, vctx)) @: _ => Susp.force vctx
     | META_APP (_, _, ms <: (_, _, vctx)) @: _ => Susp.force vctx


  local
    fun union c1 c2 = VarCtx.union c1 c2 (fn (_, l, r) => l @ r)
  in
    val rec varOccurrences =
      fn V (LN.FREE x, _) @: SOME m => VarCtx.singleton x [m]
      (* Note: this silently ignores free variables without an annotation. *)
      | V _ @: _ => VarCtx.empty
      | APP (_, es <: _) @: _ =>
        Sp.foldr (fn (ABS (_, _, m), ctx) => union ctx (varOccurrences m)) VarCtx.empty es
      | META_APP (_, _, ms <: _) @: _ =>
        Sp.foldr (fn (m, ctx) => union ctx (varOccurrences m)) VarCtx.empty ms
  end

  local
    fun union c1 c2 = SymCtx.union c1 c2 (fn (_, l, r) => l @ r)
  in
    val rec symOccurrences =
      fn V _ @: _ => SymCtx.empty
      | APP (theta, es <: _) @: m =>
        (* The annotation mechanism is not fine-grained enough to give us
         * positions of symbols themselves, but only of the applied operator.
         * See the comment in abt.sig.
         *)
        let
          val ctx0 =
            case m of
              NONE => SymCtx.empty
            | SOME m =>
              List.foldr
                (fn ((LN.FREE u, tau), ctx) => union (SymCtx.singleton u [m]) ctx
                  | (_, ctx) => ctx)
                SymCtx.empty
                (O.support theta)
        in
          Sp.foldr (fn (ABS (_, _, m), ctx) => union ctx (symOccurrences m)) ctx0 es
        end
      | META_APP (_, ps, ms <: _) @: m =>
        let
          val ctx0 =
              case m of
                NONE => SymCtx.empty
              | SOME m =>
                Sp.foldr
                  (fn ((P.VAR (LN.FREE u), tau), ctx) => union (SymCtx.singleton u [m]) ctx
                    | ((P.APP t, tau), ctx) =>
                      List.foldr
                        (fn ((LN.FREE u,sigma), ctx') => union (SymCtx.singleton u [m]) ctx'
                          | (_, ctx') => ctx')
                        ctx
                        (P.freeVars t)
                    | (_, ctx) => ctx)
                  SymCtx.empty
                  ps
        in
          Sp.foldr (fn (m, ctx) => union ctx (symOccurrences m)) ctx0 ms
        end
  end

  fun getCtx m : Ctx.ctx =
    (Susp.delay (fn _ => metactx m),
     Susp.delay (fn _ => symctx m),
     Susp.delay (fn _ => varctx m))

  fun mapAbs_ f (ABS (us, xs, m)) =
    ABS (us, xs, f m)

  fun liftTraverseAbs f coord =
    mapAbs_ (f (LnCoord.shiftRight coord))

  fun makeApp theta es =
    let
      val ctx = Sp.foldr (fn (ABS (_, _, m), ctx) => Ctx.merge (ctx, getCtx m)) Ctx.empty es
    in
      APP (theta, es <: ctx)
    end

  fun makeMetaApp (mv, tau) us ms =
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
  fun imprisonVariable (v, tau) coord : abt_internal -> abt_internal =
    fn m as V (LN.FREE v', sigma) =>
         if Var.eq (v, v') then
           (assertSortEq (sigma, tau);
            V (LN.BOUND coord, sigma))
         else
           m
     | V v => V v
     | APP (theta, es <: ctx) =>
         makeApp theta (Sp.map (liftTraverseAbs (imprisonVariableAnn (v, tau)) coord) es)
     | META_APP (mv, us, ms <: ctx) =>
         makeMetaApp mv us (Sp.map (imprisonVariableAnn (v, tau) coord) ms)

  and imprisonVariableAnn (v, tau) =
    Ann.map o imprisonVariable (v, tau)

  fun imprisonSymbol (v, tau) coord : abt_internal -> abt_internal =
    fn V v => V v
     | APP (theta, es <: ctx) =>
         let
           fun rho v' = if Sym.eq (v, v') then LN.BOUND coord else LN.FREE v'
           fun chk (LN.FREE v', tau') = if Sym.eq (v, v') then assertPSortEq (tau, tau') else ()
             | chk _ = ()
           val _ = List.app chk (O.support theta)
           val theta' = O.map (P.ret o LN.bind rho) theta
           val ctx' = Ctx.modifySyms (fn sctx => SymCtx.remove sctx v) ctx
         in
           APP (theta', Sp.map (liftTraverseAbs (imprisonSymbolAnn (v,tau)) coord) es <: ctx')
         end
     | META_APP (m, ps, Ms <: ctx) =>
         let
           fun rho v' = if Sym.eq (v, v') then LN.BOUND coord else LN.FREE v'
           fun rho' (p, s) = (P.map (LN.bind rho) p, s)
           val vs = Sp.map rho' ps
           val ctx' = Ctx.modifySyms (fn sctx => SymCtx.remove sctx v) ctx
         in
           META_APP (m, vs, Sp.map (imprisonSymbolAnn (v, tau) coord) Ms <: ctx')
         end

  and imprisonSymbolAnn (v, tau) =
    Ann.map o imprisonSymbol (v, tau)

  (* This is the reverse of the above, given a position we hunt around for
   * a bound variable in the correct slot and switch out for a free one.
   *)
  fun liberateVariable (v, sigma) coord =
    fn e as V (LN.FREE _, _) => e
     | e as V (LN.BOUND coord', sigma) =>
         if LnCoord.eq (coord, coord') then V (LN.FREE v, sigma) else e
     | APP (theta, es <: ctx) =>
         makeApp theta (Sp.map (liftTraverseAbs (liberateVariableAnn (v, sigma)) coord) es)
     | META_APP ((x, tau), us, ms <: ctx) =>
         makeMetaApp (x, tau) us (Sp.map (liberateVariableAnn (v, sigma) coord) ms)

  and liberateVariableAnn (v, sigma) =
    Ann.map o liberateVariable (v, sigma)

  fun liberateSymbol (u, sigma) coord =
    let
      fun rho (LN.BOUND coord') = if LnCoord.eq (coord, coord') then LN.FREE u else LN.BOUND coord'
        | rho u' = u'
    in
      fn e as V _ => e
       | APP (theta, es <: ctx) =>
           let
             val theta' = O.map (P.ret o rho) theta
             val fs = Sp.map (liftTraverseAbs (liberateSymbolAnn (u, sigma)) coord) es
           in
             makeApp theta' fs
           end
       | META_APP ((x, tau), ps, ms <: ctx) =>
           let
             val vs = Sp.map (fn (l, s) => (P.map rho l, s)) ps
             val ns = Sp.map (liberateSymbolAnn (u, sigma) coord) ms
             val ctx' = Ctx.modifySyms (fn sctx => SymCtx.insert sctx u sigma) ctx
           in
             makeMetaApp (x, tau) vs ns
           end
    end
  and liberateSymbolAnn (u, sigma) =
    Ann.map o liberateSymbol (u, sigma)

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
      fun cmp (f, g) (coord, a) = f (coord, g (LnCoord.shiftDown coord, a))
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
    val imprisonVariables = foldStar imprisonVariableAnn o Sp.Pair.zipEq
    val imprisonSymbols = foldStar imprisonSymbolAnn o Sp.Pair.zipEq

    val liberateVariables : (variable * sort) Sp.t -> abt -> abt =
      foldStar liberateVariableAnn

    val liberateSymbols : (symbol * psort) Sp.t -> abt -> abt =
      foldStar liberateSymbolAnn
  end


  fun checkb ((us, xs) \ m, ((ssorts, vsorts), sigma)) =
    let
      val (_, tau) = infer m
      val () = assertSortEq (sigma, tau)
    in
      ABS
        (Sp.Pair.zipEq (Sp.map Sym.toString us, ssorts),
         Sp.Pair.zipEq (Sp.map Var.toString xs, vsorts),
         imprisonSymbols (us, ssorts) (imprisonVariables (xs, vsorts) m))
    end

  and infer (M @: _) =
    case M of
         V (x, tau) => (` (LN.getFree x), tau)
       | APP (theta, Es <: _) =>
         let
           val (_, tau) = O.arity theta
           val theta' = O.map (P.ret o LN.getFree) theta
           val Es' = Sp.map (#1 o inferb) Es
         in
           (theta' $ Es', tau)
         end
       | META_APP ((mv, tau), ps, Ms <: _) =>
         let
           val ps' = Sp.map (fn (p, sigma) => (P.map LN.getFree p, sigma)) ps
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
         `x => V (LN.FREE x, sigma) @: NONE
       | theta $ es =>
           let
             val (valences, tau)  = O.arity theta
             val () = assertSortEq (sigma, tau)
             val theta' = O.map (P.ret o LN.FREE) theta
             val es' = Sp.Pair.mapEq checkb (es, valences)
           in
             makeApp theta' es' @: NONE
           end
       | x $# (ps, ms) =>
           let
             val ssorts = Sp.map #2 ps
             val vsorts = Sp.map sort ms
             val ps' = Sp.map (fn (p, tau) => (P.map LN.FREE p, tau) before (P.check tau p; ())) ps
             fun chkInf (m, tau) = (assertSortEq (tau, sort m); m)
             val ms' = Sp.Pair.mapEq chkInf (ms, vsorts)
             val ctx = Sp.foldr (fn (m, ctx) => Ctx.merge (ctx, getCtx m)) Ctx.empty ms'
           in
             makeMetaApp (x, sigma) ps' ms' @: NONE
           end

  fun $$ (theta, es) =
    let
      val (_, tau) = O.arity theta
    in
      check (theta $ es, tau)
    end

  fun mapAbs f abs =
    let
      val ((us, xs) \ m, vl) = inferb abs
    in
      checkb ((us, xs) \ f m, vl)
    end

  local
    structure OpLnEq = struct val eq = O.eq (LN.eq Sym.eq) end
  in
    (* While this looks simple by using locally nameless representations this
     * implements alpha equivalence (and is very efficient!)
     *)
    fun eq (V (v, _) @: _, V (v', _) @: _) = LN.eq Var.eq (v, v')
      | eq (APP (theta, es <: _) @: _, APP (theta', es' <: _) @: _) =
          OpLnEq.eq (theta, theta') andalso Sp.Pair.allEq eqAbs (es, es')
      | eq (META_APP ((mv, _), ps, ms <: _) @: _, META_APP ((mv', _), ps', ms' <: _) @: _) =
          Metavar.eq (mv, mv')
            andalso Sp.Pair.allEq (fn ((x, _), (y, _)) => P.eq (LN.eq Sym.eq) (x,y)) (ps, ps')
            andalso Sp.Pair.allEq eq (ms, ms')
      | eq _ = false
    and eqAbs (ABS (_, _, m), ABS (_, _, m')) = eq (m, m')
  end

  fun metaenvToString (env : metaenv) : string = 
    let
      val assignments = Metavar.Ctx.toList env
      fun f (x, abs) = Metavar.toString x ^ " := " ^ primToStringAbs abs
    in
      "{" ^ ListSpine.pretty f "; " assignments ^ "}"
    end

  exception BadSubstMetaenv of {metaenv : metaenv, term : abt, description : string}

  fun substMetaenv rho m =
    let
      val ann = getAnnotation m
      val (view, tau) = infer m
    in
      setAnnotation ann
        (case view of
             `x => m
           | theta $ es =>
               check (theta $ Sp.map (mapBind (substMetaenv rho)) es, tau)
           | mv $# (ps, ms) =>
               let
                 val ms' = Sp.map (substMetaenv rho) ms
               in
                 case MetaCtx.find rho mv of
                      NONE =>
                        check (mv $# (ps, ms'), tau)
                    | SOME abs =>
                        let
                          val (us , xs) \ m = outb abs
                          val srho =
                            Sp.foldr
                              (fn ((u, (p, _)), r) => SymCtx.insert r u p)
                              SymCtx.empty
                              (Sp.Pair.zipEq (us, ps))
                          val vrho =
                            Sp.foldr
                              (fn ((x,m), rho) => VarCtx.insert rho x m)
                              VarCtx.empty
                              (Sp.Pair.zipEq (xs, ms'))
                        in
                          substVarenv vrho (substSymenv srho m)
                        end
               end)
        handle Sp.Pair.UnequalLengths => 
          raise BadSubstMetaenv
            {metaenv = rho,
             term = m,
             description = "Tried to substitute " ^ metaenvToString rho ^ " in " ^ primToString m}
    end

  and substVarenv rho =
    Ann.map
      (fn m as V (LN.FREE x, sigma) => getOpt (Option.map Ann.unAnn (VarCtx.find rho x), m)
        | m as V _ => m
        | APP (theta, es <: _) => makeApp theta (Sp.map (mapAbs_ (substVarenv rho)) es)
        | META_APP (mv, us, ms <: _) => makeMetaApp mv us (Sp.map (substVarenv rho) ms))

  and renameVars rho =
    Ann.map
      (fn m as V (LN.FREE x, sigma) => V (LN.FREE (getOpt (VarCtx.find rho x, x)), sigma)
        | m as V _ => m
        | APP (theta, es <: _) => makeApp theta (Sp.map (mapAbs_ (renameVars rho)) es)
        | META_APP (mv, us, ms <: _) => makeMetaApp mv us (Sp.map (renameVars rho) ms))


  and substSymenv rho =
    let
      val substp =
        fn LN.FREE a => P.map LN.pure (getOpt (SymCtx.find rho a, P.ret a))
         | u => P.ret u
    in
      Ann.map
        (fn m as V _ => m
          | APP (theta, es <: _) =>
              let
                val theta' = O.map substp theta
              in
                makeApp theta' (Sp.map (mapAbs_ (substSymenv rho)) es)
              end
          | META_APP (mv, ps, ms <: _) =>
              let
                fun ren' (p, s) = (P.bind substp p, s)
              in
                makeMetaApp mv (Sp.map ren' ps) (Sp.map (substSymenv rho) ms)
              end)
    end


  fun unbind abs ps ms =
    let
      val (vs, xs) \ m = outb abs
      val srho =
        Sp.foldr
          (fn ((v,p), rho) => SymCtx.insert rho v p)
          SymCtx.empty
          (Sp.Pair.zipEq (vs, ps))
      val vrho =
        Sp.foldr
          (fn ((x,m), rho) => VarCtx.insert rho x m)
          VarCtx.empty
          (Sp.Pair.zipEq (xs, ms))
    in
      substVarenv vrho (substSymenv srho m)
    end

  fun // (abs, (ps, ms)) =
    unbind abs ps ms


  fun substVar (n, x) = substVarenv (VarCtx.insert VarCtx.empty x n)
  fun substMetavar (e, mv) = substMetaenv (MetaCtx.insert MetaCtx.empty mv e)
  fun substSymbol (p, u) = substSymenv (SymCtx.insert SymCtx.empty u p)

  fun mapSubterms f m =
    let
      val (view, tau) = infer m
    in
      setAnnotation (getAnnotation m) (check (map f view, tau))
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

    fun unifySymbols (u, v, rho) =
      case (u, v) of
          (LN.FREE u', LN.FREE v') =>
            SymRenUtil.extend rho (u', v')
        | (LN.BOUND i, LN.BOUND j) =>
            if LnCoord.eq (i, j) then
              rho
            else
              raise UnificationFailed
        | _ => raise UnificationFailed

    fun unifyParams (p, q, rho) =
      case (p, q) of
         (P.VAR u, P.VAR v) => unifySymbols (u, v, rho)
       | (P.APP t1, P.APP t2) =>
           (* check if the head operators are equal *)
           if P.Sig.eq (fn _ => true) (t1, t2) then
             (* unify subterms *)
             ListPair.foldrEq unifyParams rho (P.collectSubterms t1, P.collectSubterms t2)
           else
             raise UnificationFailed
       | _ => raise UnificationFailed

    fun unifyOperator rho (theta1 : LN.operator, theta2 : LN.operator) : symbol SymCtx.dict =
      if O.eq (fn _ => true) (theta1, theta2) then
        let
          val us = List.map #1 (O.support theta1)
          val vs = List.map #1 (O.support theta2)
        in
          ListPair.foldlEq unifySymbols rho (us, vs)
        end
      else
        raise UnificationFailed

    local
      fun go (mrho, srho, vrho) =
        fn (V (LN.FREE x, sigma) @: _, V (LN.FREE y, tau) @: _) =>
             if S.eq (sigma, tau) then
               (mrho, srho, VarRenUtil.extend vrho (x, y))
             else
               raise UnificationFailed
         | (V (LN.BOUND i, _) @: _, V (LN.BOUND j, _) @: _) =>
             if LnCoord.eq (i, j) then
               (mrho, srho, vrho)
             else
               raise UnificationFailed
         | (APP (theta1, es1 <: _) @: _, APP (theta2, es2 <: _) @: _) =>
             let
               val srho' = unifyOperator srho (theta1, theta2)
             in
               Sp.foldr
                 (fn ((ABS (_, _, m1), ABS (_, _, m2)), acc) => go acc (m1, m2))
                 (mrho, srho', vrho)
                 (Sp.Pair.zipEq (es1, es2))
             end
         | (META_APP ((x1, tau1), ps1, ms1 <: _) @: _, META_APP ((x2, tau2), ps2, ms2 <: _) @: _) =>
             let
               val _ = if S.eq (tau1, tau2) then () else raise UnificationFailed
               val mrho' = MetaRenUtil.extend mrho (x1, x2)
               val srho' =
                 Sp.foldr
                   (fn (((p, _), (q, _)), rho) => unifyParams (p, q, rho))
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

functor SimpleAbt (O : ABT_OPERATOR) =
  Abt (structure Sym = AbtSymbol ()
       structure Var = AbtSymbol ()
       structure Metavar = AbtSymbol ()
       structure O = O
       type annotation = unit)
