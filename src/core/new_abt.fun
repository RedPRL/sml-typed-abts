functor NewAbt
  (structure Sym : ABT_SYMBOL
   structure Var : ABT_SYMBOL
   structure Metavar : ABT_SYMBOL
   structure O : ABT_OPERATOR where type 'a Ar.Vl.Sp.t = 'a list
   type user_annotation) : ABT =
struct
  exception todo
  fun ?e = raise e

  structure Sym = Sym and Var = Var and Metavar = Metavar and O = O

  structure S = O.Ar.Vl.S and PS = O.Ar.Vl.PS and Valence = O.Ar.Vl
  structure MetaCtxUtil = ContextUtil (structure Ctx = Metavar.Ctx and Elem = Valence)
  structure VarCtxUtil = ContextUtil (structure Ctx = Var.Ctx and Elem = S)
  structure SymCtxUtil = ContextUtil (structure Ctx = Sym.Ctx and Elem = PS)

  type sort = O.Ar.Vl.S.t
  type psort = O.Ar.Vl.PS.t

  structure P = O.P
  type param = Sym.t P.term

  structure Sc = LnScope (structure Sym = Sym and Var = Var and Metavar = Metavar type psort = psort type sort = sort)
  datatype 'a locally =
     FREE of 'a
   | BOUND of int

  type symbol = Sym.t
  type variable = Var.t
  type metavariable = Metavar.t
  type operator = symbol O.t
  type valence = O.Ar.valence
  type varctx = sort Var.Ctx.dict
  type symctx = psort Sym.Ctx.dict
  type metactx = valence Metavar.Ctx.dict

  structure Views = AbtViews (ListSpine)
  open Views

  type 'a view = (param, psort, symbol, variable, metavariable, operator, 'a) termf
  type 'a bview = (symbol, variable, 'a) bindf
  type 'a appview = (symbol, variable, operator, 'a) appf

  infixr 5 \
  infix 5 $ $#

  type system_annotation =
    {symIdxBound: int option,
     varIdxBound: int option,
     metaIdxBound: int option,
     freeVars: varctx,
     freeSyms: symctx,
     hasFreeMetas: bool}

  type annotation =
    {user: user_annotation option,
     system: system_annotation}

  val optionalIdxLub =
    fn (SOME i, SOME j) => SOME (Int.max (i, j))
     | (SOME i, NONE) => SOME i
     | (NONE, SOME i) => SOME i
     | (NONE, NONE) => NONE

  fun systemAnnLub (ann1 : system_annotation, ann2 : system_annotation) : system_annotation =
    {symIdxBound = optionalIdxLub (#symIdxBound ann1, #symIdxBound ann2),
     varIdxBound = optionalIdxLub (#varIdxBound ann1, #varIdxBound ann2),
     metaIdxBound = optionalIdxLub (#metaIdxBound ann1, #metaIdxBound ann2),
     freeVars = VarCtxUtil.union (#freeVars ann1, #freeVars ann2),
     freeSyms = SymCtxUtil.union (#freeSyms ann1, #freeSyms ann2),
     hasFreeMetas = #hasFreeMetas ann1 orelse #hasFreeMetas ann2}

  datatype 'a annotated = <: of 'a * annotation
  infix <:

  datatype abt_internal =
     V of var_term
   | APP of app_term
   | META of meta_term
  withtype abt = abt_internal annotated
  and var_term = Var.t locally * sort
  and app_term = Sym.t locally O.t * abt Sc.scope list
  and meta_term = (Metavar.t locally * sort) * (Sym.t locally P.term * psort) list * abt list

  type abs = abt Sc.scope
  type metaenv = abs Metavar.Ctx.dict
  type varenv = abt Var.Ctx.dict
  type symenv = param Sym.Ctx.dict

  val sort =
    fn V (_, tau) <: _ => tau
     | APP (theta, _) <: _ => #2 (O.arity theta)
     | META ((_, tau), _, _) <: _ => tau


  (* TODO: add diagnostics *)
  exception BadInstantiate


  type 'a binding_support = (abt, Sym.t locally P.term, 'a) Sc.binding_support

  fun scopeReadAnn scope =
    let
      val Sc.\ ((us, xs), body <: ann) = Sc.unsafeRead scope
      val {symIdxBound, varIdxBound, metaIdxBound, freeVars, freeSyms, hasFreeMetas} = #system ann
      val symIdxBound' = Option.map (fn i => i - List.length us) symIdxBound
      val varIdxBound' = Option.map (fn i => i - List.length xs) varIdxBound
    in
      {user = #user ann,
       system = {symIdxBound = symIdxBound', varIdxBound = varIdxBound', metaIdxBound = metaIdxBound, freeSyms = freeSyms, freeVars = freeVars, hasFreeMetas = hasFreeMetas}}
    end

  fun makeVarTerm (var, tau) userAnn =
    case var of
       FREE x =>
         V (var, tau) <:
           {user = userAnn,
            system = {symIdxBound = NONE,varIdxBound = NONE, metaIdxBound = NONE, freeVars = Var.Ctx.singleton x tau, freeSyms = Sym.Ctx.empty, hasFreeMetas = false}}

     | BOUND i =>
         V (var, tau) <:
           {user = userAnn,
            system = {symIdxBound = NONE, varIdxBound = SOME (i + 1), metaIdxBound = NONE, freeVars = Var.Ctx.empty, freeSyms = Sym.Ctx.empty, hasFreeMetas = false}}

  fun idxBoundForSyms support =
    List.foldr
      (fn ((FREE _,_), oidx) => oidx
        | ((BOUND i, _), NONE) => SOME (i + 1)
        | ((BOUND i, _), SOME j) => SOME (Int.max (i, j)))
      NONE
      support

  fun freeSymsForSupport support = 
    List.foldl
      (fn ((FREE u, tau), ctx) => Sym.Ctx.insert ctx u tau
        | (_, ctx) => ctx)
      Sym.Ctx.empty
      support

  fun makeAppTerm (theta, scopes) userAnn =
    let
      val support = O.support theta
      val freeSyms = freeSymsForSupport support
      val symIdxBound = idxBoundForSyms support
      val operatorAnn = {symIdxBound = symIdxBound, varIdxBound = NONE, metaIdxBound = NONE, freeVars = Var.Ctx.empty, freeSyms = freeSyms, hasFreeMetas = false}
      val systemAnn =
        List.foldr
          (fn (scope, ann) => systemAnnLub (ann, #system (scopeReadAnn scope)))
          operatorAnn
          scopes
    in
      APP (theta, scopes) <: {user = userAnn, system = systemAnn}
    end

  val paramSystemAnn =
    fn (P.VAR (FREE x), sigma) => {symIdxBound = NONE, varIdxBound = NONE, metaIdxBound = NONE, freeVars = Var.Ctx.empty, freeSyms = Sym.Ctx.singleton x sigma, hasFreeMetas = false}
     | (P.VAR (BOUND i), _) => {symIdxBound = SOME (i + 1), varIdxBound = NONE, metaIdxBound = NONE, freeVars = Var.Ctx.empty, freeSyms = Sym.Ctx.empty, hasFreeMetas = false}
     | (P.APP t, sigma) =>
        let
          val support = P.freeVars t
        in
          {symIdxBound = idxBoundForSyms support, varIdxBound = NONE, metaIdxBound = NONE, freeVars = Var.Ctx.empty, freeSyms = freeSymsForSupport support, hasFreeMetas = false}
        end

  fun makeMetaTerm (((meta, tau), rs, ms) : meta_term) userAnn =
    let
      val (metaIdxBound, hasFreeMetas) = case meta of FREE _ => (NONE, true) | BOUND j => (SOME (j + 1), false)
      val metaSystemAnn = {symIdxBound = NONE, varIdxBound = NONE, metaIdxBound = metaIdxBound, freeVars = Var.Ctx.empty, freeSyms = Sym.Ctx.empty, hasFreeMetas = hasFreeMetas}
      val systemAnn =
        List.foldr
          (fn ((p, sigma), ann) => systemAnnLub (ann, paramSystemAnn (p, sigma)))
          metaSystemAnn
          rs
      val systemAnn =
        List.foldr
          (fn (_ <: termAnn, ann) => systemAnnLub (ann, #system termAnn))
          systemAnn
          ms
    in
      META ((meta, tau), rs, ms) <: {user = userAnn, system = systemAnn}
    end

  local
    fun indexOfFirst pred xs =
      let
        fun aux (i, []) = NONE
          | aux (i, x::xs) = if pred x then SOME i else aux (i + 1, xs)
      in
        aux (0, xs)
      end

    fun mapFst f (x, y) =
      (f x, y)

    fun findInstantiation i items var =
      case var of
         FREE _ => NONE
       | BOUND i' =>
         let
           val i'' = i' - i
         in
           if i'' >= 0 andalso i'' < List.length items then
             SOME (List.nth (items, i''))
           else
             NONE
         end

    type 'a monoid = {unit : 'a, mul : 'a * 'a -> 'a}

    type ('p, 'a) abt_algebra =
      {handleSym : int -> (symbol locally * psort) annotated -> 'p,
       handleVar : int -> var_term annotated -> 'a,
       handleMeta : int * int * int -> meta_term annotated -> 'a,
       shouldTraverse : int * int * int -> system_annotation -> bool}

    fun abtRec (alg : (symbol locally P.t, abt) abt_algebra) (i, j, k) (term <: (ann as {user, system})) : abt =
      if not (#shouldTraverse alg (i, j, k) system) then term <: ann else
      case term of
         V (var, tau) => #handleVar alg j ((var, tau) <: ann)
       | APP (theta, args) =>
         let
           val theta' = O.mapWithSort (fn (u, sigma) => #handleSym alg i ((u, sigma) <: ann)) theta
           val args' = List.map (Sc.liftTraversal (abtRec alg) (i, j, k)) args
         in
           makeAppTerm (theta', args') user
         end
       | META ((X, tau), rs, ms) =>
         let
           val rs' = List.map (fn (r, sigma) => (P.bind (fn u => #handleSym alg i ((u, sigma) <: ann)) r, sigma)) rs
           val ms' = List.map (abtRec alg (i, j, k)) ms
         in
           #handleMeta alg (i, j, k) (((X, tau), rs', ms') <: ann)
         end

    fun abtAccum (acc : 'a monoid) (alg : ('a, 'a) abt_algebra) (i, j, k) (term <: (ann as {user, system})) : 'a =
      if not (#shouldTraverse alg (i, j, k) system) then #unit acc else
      case term of
         V var => #handleVar alg j (var <: ann)
       | APP (theta, args) =>
         let
           val support = O.support theta
           val memo = List.foldr (fn ((u, sigma), memo) => #mul acc (#handleSym alg i ((u, sigma) <: ann), memo)) (#unit acc) support
         in
           List.foldr
             (fn (scope, memo) => #mul acc (Sc.unsafeReadBody (Sc.liftTraversal (abtAccum acc alg) (i, j, k) scope), memo))
             memo
             args
         end
       | META ((X, tau), rs, ms) =>
         let
           val memo =
             List.foldr
               (fn ((r, sigma), memo) =>
                  let
                    val support = case r of P.VAR u => [(u, sigma)] | P.APP t => P.freeVars t
                  in
                    List.foldr (fn ((u, sigma), memo) => #mul acc (#handleSym alg i ((u, sigma) <: ann), memo)) memo support
                  end)
               (#unit acc)
               rs
           val memo' = List.foldr (fn (m, memo) => #mul acc (abtAccum acc alg (i, j, k) m, memo)) memo ms
         in
           #mul acc (#handleMeta alg (i, j, k) (((X, tau), rs, ms) <: ann), memo')
         end

  in
    fun instantiateAbt (i, j, k) (rs, ms, scopes) =
      let
        (* TODO: sort checking? *)
        fun instantiateSym i rs ((sym, _) <: _) =
          case findInstantiation i rs sym of
             SOME r => r
           | NONE => P.ret sym

        fun instantiateVar j ms ((var, tau) <: ann) =
          case findInstantiation j ms var of
             SOME m => if O.Ar.Vl.S.eq (sort m, tau) then m else raise BadInstantiate
           | NONE => V (var, tau) <: ann

        fun shouldTraverse (i, j, k) ({symIdxBound, varIdxBound, metaIdxBound, ...} : system_annotation) =
          let
            (* TODO: check this logic. If there is no bound (sym, var, meta), then we have nothing to instantiate. does that make sense? *)
            val needSyms = case symIdxBound of SOME i' => i < i' | NONE => false
            val needVars = case varIdxBound of SOME j' => j < j' | NONE => false
            val needMetas = case metaIdxBound of SOME k' => k < k' | NONE => false
          in
            needSyms orelse needVars orelse needMetas
          end

        fun instantiateMeta (i, j, k) ((((X, tau), rsX, msX) : meta_term) <: ann) =
          case findInstantiation k scopes X of
             SOME scope => instantiateAbt (i, j, k) (List.map #1 rsX, msX, scopes) (Sc.unsafeReadBody scope)
           | NONE => makeMetaTerm ((X, tau), rsX, msX) (#user ann)

        val alg =
          {handleSym = fn i => instantiateSym i rs,
           handleVar = fn j => instantiateVar j ms,
           handleMeta = instantiateMeta,
           shouldTraverse = shouldTraverse}
      in
        abtRec alg (i, j, k)
      end

    fun abstractAbt (i, j, k) (us, xs, Xs) =
      let
        fun shouldTraverse (i, j, k) ({freeSyms, freeVars, hasFreeMetas, ...} : system_annotation) =
          let
            val needSyms = case us of [] => false | _ => not (Sym.Ctx.isEmpty freeSyms)
            val needVars = case xs of [] => false | _ => not (Var.Ctx.isEmpty freeVars)
            val needMetas = case Xs of [] => true | _ => hasFreeMetas
          in
            needSyms orelse needVars orelse needMetas
          end

        fun abstractSym i us =
          fn (FREE u, _) <: _ =>
             (case indexOfFirst (fn v => Sym.eq (u, v)) us of
                 NONE => FREE u
               | SOME i' => BOUND (i + i'))
           | (BOUND i', _) <: _ => BOUND i'

        fun abstractVar j xs =
          fn (FREE x, tau) <: ann =>
             (case indexOfFirst (fn y => Var.eq (x, y)) xs of
                 NONE => V (FREE x, tau) <: ann
               | SOME j' => makeVarTerm (BOUND (j + j'), tau) (#user ann))
           | (BOUND j', tau) <: ann => V (BOUND j', tau) <: ann

        fun abstractMeta (i, j, k) ((((X, tau), rs, ms) : meta_term) <: ann) =
          case X of
              FREE X =>
              (case indexOfFirst (fn Y => Metavar.eq (X, Y)) Xs of
                 NONE => META ((FREE X, tau), rs, ms) <: ann
               | SOME k' => META ((BOUND (k + k'), tau), rs, ms) <: ann)
            | BOUND k' => META ((X, tau), rs, ms) <: ann

        val alg =
          {handleSym = fn i => P.ret o abstractSym i us,
           handleVar = fn j => abstractVar j xs,
           handleMeta = abstractMeta,
           shouldTraverse = shouldTraverse}
      in
        abtRec alg (i, j, k)
      end

    fun subst (srho: symenv, vrho : varenv, mrho : metaenv) =
      let
        fun shouldTraverse _ ({freeVars, freeSyms, hasFreeMetas, ...} : system_annotation) =
          let
            val needSyms = not (Sym.Ctx.isEmpty freeSyms orelse Sym.Ctx.isEmpty srho)
            val needVars = not (Var.Ctx.isEmpty freeVars orelse Var.Ctx.isEmpty vrho)
            val needMetas = hasFreeMetas andalso not (Metavar.Ctx.isEmpty mrho)
          in
            needSyms orelse needVars orelse needMetas
          end

        fun handleSym _ ((sym, sigma) <: _) =
          case sym of
             FREE u =>
             (case Sym.Ctx.find srho u of
                 NONE => P.ret sym
               | SOME r => P.map FREE r)
           | BOUND _ => P.ret sym

        fun handleVar _ ((var, tau) <: ann) =
          case var of
             FREE x =>
             (case Var.Ctx.find vrho x of
                 NONE => V (var, tau) <: ann
               | SOME m => m)
           | BOUND _ => V (var, tau) <: ann

        fun handleMeta _ (((X : metavariable locally, tau), rs, ms) <: ann) =
          case X of
             FREE X =>
             (case Metavar.Ctx.find mrho X of
                 NONE => META ((FREE X, tau), rs, ms) <: ann
               | SOME scope => instantiateAbt (0,0,0) (List.map #1 rs, ms, []) (Sc.unsafeReadBody scope))
           | BOUND _ => META ((X, tau), rs, ms) <: ann

        val alg =
          {handleSym = handleSym,
           handleVar = handleVar,
           handleMeta = handleMeta,
           shouldTraverse = shouldTraverse}
      in
        abtRec alg (0,0,0)
      end

    fun varctx (_ <: {system = {freeVars, ...}, ...}) = 
      freeVars

    fun symctx (_ <: {system = {freeSyms, ...}, ...}) = 
      freeSyms

    val metactx =
      let
        fun handleMeta _ =
          fn (((FREE x, tau), rs, ms) : meta_term) <: _ => Metavar.Ctx.singleton x ((List.map #2 rs, List.map sort ms), tau)
           | _ => Metavar.Ctx.empty

        val monoid =
          {unit = Metavar.Ctx.empty,
           mul = MetaCtxUtil.union}

        val alg =
          {handleSym = fn _ => fn _ => Metavar.Ctx.empty,
           handleVar = fn _ => fn _ => Metavar.Ctx.empty,
           handleMeta = handleMeta,
           shouldTraverse = fn _ => fn ({hasFreeMetas, ...} : system_annotation) => hasFreeMetas}
      in
        abtAccum monoid alg (0,0,0)
      end

    val symOccurrences = 
      let
        fun handleSym _ ((sym, _) <: ann) =
          case sym of 
             FREE u => Sym.Ctx.singleton u [ann]
           | _ => Sym.Ctx.empty

        val monoid : annotation list Sym.Ctx.dict monoid =
          {unit = Sym.Ctx.empty,
           mul = fn (xs1, xs2) => Sym.Ctx.union xs1 xs2 (fn (_, anns1, anns2) => anns1 @ anns2)}

        val alg =
          {handleSym = handleSym,
           handleVar = fn _ => fn _ => Sym.Ctx.empty,
           handleMeta = fn _ => fn _ => Sym.Ctx.empty,
           shouldTraverse = fn _ => fn ({freeSyms, ...} : system_annotation) => not (Sym.Ctx.isEmpty freeSyms)}
      in
        abtAccum monoid alg (0,0,0)
      end

    val varOccurrences = 
      let
        fun handleVar _ ((var, _) <: ann) =
          case var of 
             FREE x => Var.Ctx.singleton x [ann]
           | _ => Var.Ctx.empty

        val monoid : annotation list Var.Ctx.dict monoid =
          {unit = Var.Ctx.empty,
           mul = fn (xs1, xs2) => Var.Ctx.union xs1 xs2 (fn (_, anns1, anns2) => anns1 @ anns2)}

        val alg =
          {handleSym = fn _ => fn _ => Var.Ctx.empty,
           handleVar = handleVar,
           handleMeta = fn _ => fn _ => Var.Ctx.empty,
           shouldTraverse = fn _ => fn ({freeVars, ...} : system_annotation) => not (Var.Ctx.isEmpty freeVars)}
      in 
        abtAccum monoid alg (0,0,0)
      end

    fun renameVars vrho = 
      let
        fun handleVar _ ((var, tau) <: ann) = 
          case var of
             FREE x =>
             (case Var.Ctx.find vrho x of 
                 SOME y => V (FREE y, tau) <: ann
               | NONE => V (var, tau) <: ann)
           | _ => V (var, tau) <: ann

        val alg =
          {handleSym = fn _ => fn (sym, tau) <: ann => P.ret sym,
           handleVar = handleVar,
           handleMeta = fn _ => fn meta <: ann => META meta <: ann,
           shouldTraverse = fn _ => fn ({freeVars, ...} : system_annotation) => not (Var.Ctx.isEmpty freeVars)}
      in
        abtRec alg (0,0,0)
      end
  end

  exception BadSubstMetaenv of {metaenv : metaenv, term : abt, description : string}

  fun substVarenv vrho =
    subst (Sym.Ctx.empty, vrho, Metavar.Ctx.empty)

  fun substSymenv srho =
    subst (srho, Var.Ctx.empty, Metavar.Ctx.empty)

  fun substMetaenv mrho =
    subst (Sym.Ctx.empty, Var.Ctx.empty, mrho)

  fun substVar (m, x) =
    substVarenv (Var.Ctx.singleton x m)

  fun substSymbol (r, u) =
    substSymenv (Sym.Ctx.singleton u r)

  fun substMetavar (scope, X) =
    substMetaenv (Metavar.Ctx.singleton X scope)

  fun annotate _ = ?todo
  fun getAnnotation _ = ?todo
  fun setAnnotation _ = ?todo
  fun clearAnnotation _ = ?todo



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

  val abtBindingSupport = 
    {abstract = abstractAbt,
     instantiate = instantiateAbt,
     freeVariable = fn (x, tau) => makeVarTerm (FREE x, tau) NONE,
     freeSymbol = fn u => P.ret (FREE u)}

  fun checkb ((us, xs) \ m, ((ssorts, vsorts), tau)) : abs =
    let
      val (_, tau') = infer m
      val () = assertSortEq (tau, tau')
    in
      (* TODO: this doesn't check sort for these variables *)
      Sc.intoScope (abtBindingSupport) (Sc.\ ((us, xs), m))
    end

  and infer _ = ?todo


  fun unbind _ = ?todo
  fun // _ = ?todo
  fun $$ _ = ?todo

  fun check _ = ?todo
  fun out _ = ?todo
  fun eqAbs _ = ?todo
  fun mapAbs _ = ?todo
  fun abtToAbs _ = ?todo
  fun mapSubterms _ = ?todo
  fun deepMapSubterms _ = ?todo
  fun eq _ = ?todo
  fun inferb _ = ?todo
  fun outb _ = ?todo
  fun valence _ = ?todo
  fun primToString _ = ?todo
  fun primToStringAbs _ = ?todo
end