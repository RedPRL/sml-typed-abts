functor NewAbt
  (structure Sym : ABT_SYMBOL
   structure Var : ABT_SYMBOL
   structure Metavar : ABT_SYMBOL
   structure O : ABT_OPERATOR where type 'a Ar.Vl.Sp.t = 'a list
   type annotation) : ABT =
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
     freeMetas: metactx}

  type annotation = annotation
  type internal_annotation =
    {user: annotation option,
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
     freeMetas = MetaCtxUtil.union (#freeMetas ann1, #freeMetas ann2)}

  datatype 'a annotated = <: of 'a * internal_annotation
  infix <:

  datatype abt_internal =
     V of var_term
   | APP of app_term
   | META of meta_term
  and abs = ABS of psort list * sort list * abt Sc.scope
  withtype abt = abt_internal annotated
  and var_term = Var.t locally * sort
  and app_term = Sym.t locally O.t * abs list
  and meta_term = (Metavar.t locally * sort) * (Sym.t locally P.term * psort) list * abt_internal annotated list

  fun locallyToString f = 
    fn FREE x => f x
     | BOUND i => "<" ^ Int.toString i ^ ">"

  val rec primToString =
    fn V (v, _) <: _ => locallyToString Var.toString v
     | APP (theta, es) <: _ =>
         O.toString (locallyToString Sym.toString) theta
           ^ "("
           ^ ListSpine.pretty primToStringAbs "; " es
           ^ ")"
     | META ((X, tau), ps, ms) <: _ =>
         "#" ^ locallyToString Metavar.toString X
           ^ "{" ^ ListSpine.pretty (P.toString (locallyToString Sym.toString) o #1) ", " ps ^ "}"
           ^ "[" ^ ListSpine.pretty primToString ", " ms ^ "]"
  and primToStringAbs =
    fn ABS (ssorts, vsorts, m) =>
      "{" ^ ListSpine.pretty PS.toString ", " ssorts ^ "}"
      ^ "[" ^ ListSpine.pretty S.toString ", " vsorts ^ "]"
      ^ "." ^ primToString (Sc.unsafeReadBody m)


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
      val {symIdxBound, varIdxBound, metaIdxBound, freeVars, freeSyms, freeMetas} = #system ann
      val symIdxBound' = Option.map (fn i => i - List.length us) symIdxBound
      val varIdxBound' = Option.map (fn i => i - List.length xs) varIdxBound
    in
      {user = #user ann,
       system = {symIdxBound = symIdxBound', varIdxBound = varIdxBound', metaIdxBound = metaIdxBound, freeSyms = freeSyms, freeVars = freeVars, freeMetas = freeMetas}}
    end

  fun makeVarTerm (var, tau) userAnn =
    case var of
       FREE x =>
         V (var, tau) <:
           {user = userAnn,
            system = {symIdxBound = NONE,varIdxBound = NONE, metaIdxBound = NONE, freeVars = Var.Ctx.singleton x tau, freeSyms = Sym.Ctx.empty, freeMetas = Metavar.Ctx.empty}}

     | BOUND i =>
         V (var, tau) <:
           {user = userAnn,
            system = {symIdxBound = NONE, varIdxBound = SOME (i + 1), metaIdxBound = NONE, freeVars = Var.Ctx.empty, freeSyms = Sym.Ctx.empty, freeMetas = Metavar.Ctx.empty}}

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
      val operatorAnn = {symIdxBound = symIdxBound, varIdxBound = NONE, metaIdxBound = NONE, freeVars = Var.Ctx.empty, freeSyms = freeSyms, freeMetas = Metavar.Ctx.empty}
      val systemAnn =
        List.foldr
          (fn (ABS (_, _, scope), ann) => systemAnnLub (ann, #system (scopeReadAnn scope)))
          operatorAnn
          scopes
    in
      APP (theta, scopes) <: {user = userAnn, system = systemAnn}
    end

  fun paramSystemAnn (r, sigma) =
    let
      val support = P.check sigma r
    in
      {symIdxBound = idxBoundForSyms support, varIdxBound = NONE, metaIdxBound = NONE, freeVars = Var.Ctx.empty, freeSyms = freeSymsForSupport support, freeMetas = Metavar.Ctx.empty}
    end

  (* For some reason, this is not setting the de-idx bounds properly in the system annotation *)
  fun makeMetaTerm (((meta, tau), rs, ms) : meta_term) userAnn =
    let
      val (metaIdxBound, freeMetas) =
        case meta of
           FREE X => (NONE, Metavar.Ctx.singleton X ((List.map #2 rs, List.map sort ms), tau))
         | BOUND j => (SOME (j + 1), Metavar.Ctx.empty)

      val metaSystemAnn = {symIdxBound = NONE, varIdxBound = NONE, metaIdxBound = metaIdxBound, freeVars = Var.Ctx.empty, freeSyms = Sym.Ctx.empty, freeMetas = freeMetas}
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


  fun mapFst f (x, y) =
    (f x, y)

  local
    fun indexOfFirst pred xs =
      let
        fun aux (i, []) = NONE
          | aux (i, x::xs) = if pred x then SOME i else aux (i + 1, xs)
      in
        aux (0, xs)
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
           val args' = List.map (fn ABS (ssorts, vsorts, scope) => ABS (ssorts, vsorts, Sc.liftTraversal (abtRec alg) (i, j, k) scope)) args
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
             (fn (ABS (_, _, scope), memo) => #mul acc (Sc.unsafeReadBody (Sc.liftTraversal (abtAccum acc alg) (i, j, k) scope), memo))
             memo
             args
         end
       | META ((X, tau), rs, ms) =>
         let
           val memo =
             List.foldr
               (fn ((r, sigma), memo) =>
                  let
                    val support = P.check sigma r
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

        fun instantiateSym i ((sym, sigma) <: _) =
          case findInstantiation i rs sym of
             SOME r => (P.check sigma r; r)
           | NONE => P.ret sym

        fun instantiateVar j ((var, tau) <: ann) =
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
            (* TODO: this logic was incorect!*)
            true
            (* needSyms orelse needVars orelse needMetas *)
          end

        (* It is weird that this has to be recursive at this spot *)
        fun instantiateMeta (i, j, k) ((((X, tau), rsX, msX) : meta_term) <: ann) =
          case findInstantiation k scopes X of
             SOME scope => instantiateAbt (0, 0, 0) (List.map #1 rsX, msX, scopes) (Sc.unsafeReadBody scope)
           | NONE => makeMetaTerm ((X, tau), rsX, msX) (#user ann)

        val alg =
          {handleSym = instantiateSym,
           handleVar = instantiateVar,
           handleMeta = instantiateMeta,
           shouldTraverse = shouldTraverse}
      in
        abtRec alg (i, j, k)
      end

    fun abstractAbt (i, j, k) (us, xs, Xs) =
      let
        fun shouldTraverse (i, j, k) ({freeSyms, freeVars, freeMetas, ...} : system_annotation) =
          let
            val needSyms = case us of [] => false | _ => not (Sym.Ctx.isEmpty freeSyms)
            val needVars = case xs of [] => false | _ => not (Var.Ctx.isEmpty freeVars)
            val needMetas = case Xs of [] => false | _ => not (Metavar.Ctx.isEmpty freeMetas)
          in
            needSyms orelse needVars orelse needMetas
          end

        fun abstractSym i =
          fn (sym as FREE u, _) <: _ =>
             (case indexOfFirst (fn v => Sym.eq (u, v)) us of
                 NONE => P.ret sym
               | SOME i' => P.ret (BOUND (i + i')))
           | (sym, _) <: _ => P.ret sym

        fun abstractVar j =
          fn (vt as (FREE x, tau)) <: ann =>
             (case indexOfFirst (fn y => Var.eq (x, y)) xs of
                 NONE => V vt <: ann
               | SOME j' => makeVarTerm (BOUND (j + j'), tau) (#user ann))
           | vt <: ann => V vt <: ann

        fun abstractMeta (i, j, k) ((meta as (((X, tau), rs, ms) : meta_term)) <: ann) =
          case X of
              FREE X =>
              (case indexOfFirst (fn Y => Metavar.eq (X, Y)) Xs of
                 NONE => META meta <: ann
               | SOME k' => META ((BOUND (k + k'), tau), rs, ms) <: ann)
            | BOUND k' => META meta <: ann

        val alg =
          {handleSym = abstractSym,
           handleVar = abstractVar,
           handleMeta = abstractMeta,
           shouldTraverse = shouldTraverse}
      in
        abtRec alg (i, j, k)
      end


   val abtBindingSupport = 
    {abstract = abstractAbt,
     instantiate = instantiateAbt,
     freeVariable = fn (x, tau) => makeVarTerm (FREE x, tau) NONE,
     freeSymbol = fn u => P.ret (FREE u)}

    fun subst (srho: symenv, vrho : varenv, mrho : metaenv) =
      let
        fun shouldTraverse _ ({freeVars, freeSyms, freeMetas, ...} : system_annotation) =
          let
            val needSyms = not (Sym.Ctx.isEmpty freeSyms orelse Sym.Ctx.isEmpty srho)
            val needVars = not (Var.Ctx.isEmpty freeVars orelse Var.Ctx.isEmpty vrho)
            val needMetas = not (Metavar.Ctx.isEmpty freeMetas orelse Metavar.Ctx.isEmpty mrho)
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

        fun handleVar _ ((vt as (var, tau)) <: ann) =
          case var of
             FREE x =>
             (case Var.Ctx.find vrho x of
                 NONE => V vt <: ann
               | SOME m => m)
           | BOUND _ => V vt <: ann

        fun handleMeta (i, j, k) ((meta as ((X : metavariable locally, tau), rs, ms)) <: ann) =
          case X of
             FREE X =>
             (case Metavar.Ctx.find mrho X of
                 NONE => META meta <: ann
               | SOME (ABS (_, _, scope)) => instantiateAbt (0,0,0) (List.map #1 rs, ms, []) (Sc.unsafeReadBody scope))
           | BOUND _ => META meta <: ann

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

    fun metactx (_ <: {system = {freeMetas, ...}, ...}) =
      freeMetas

    val symOccurrences : abt -> annotation list Sym.ctx = 
      let
        fun handleSym _ ((sym, _) <: {user, system}) =
          case (sym, user) of 
             (FREE u, SOME ann) => Sym.Ctx.singleton u [ann]
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
        fun handleVar _ ((var, _) <: {user, system}) =
          case (var, user) of 
             (FREE x, SOME ann) => Var.Ctx.singleton x [ann]
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


  fun annotate ann (m <: {system, ...}) = m <: {user = SOME ann, system = system}
  fun getAnnotation (_ <: {user, ...}) = user
  fun setAnnotation ann (m <: {system, ...}) = m <: {user = ann, system = system}
  fun clearAnnotation (m <: {system, ...}) = m <: {user = NONE, system = system}

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


  fun checkb ((us, xs) \ m, ((ssorts, vsorts), tau)) : abs =
    let
      val (_, tau') = infer m

      val syms = symctx m
      val vars = varctx m
    in
      assertSortEq (tau, tau');
      ListPair.appEq (fn (u, sigma) => assertPSortEq (sigma, Option.getOpt (Sym.Ctx.find syms u, sigma))) (us, ssorts);
      ListPair.appEq (fn (x, tau) => assertSortEq (tau, Option.getOpt (Var.Ctx.find vars x, tau))) (xs, vsorts);
      ABS (ssorts, vsorts, Sc.intoScope abtBindingSupport (Sc.\ ((us, xs), m)))
    end

  and infer (term <: ann) =
    case term of 
       V (FREE x, tau) => (`x, tau)
     | V _ => raise Fail "I am a number, not a free variable!!"
     | APP (theta, args) =>
       let
         val (vls, tau) = O.arity theta
         val theta' = O.map (fn FREE u => P.ret u | _ => raise Fail ("infer/App: Did not expect bound symbol in term " ^ primToString (term <: ann))) theta
         val args' = List.map outb args
       in
         (theta' $ args', tau)
       end
     | META ((FREE X, tau), rs, ms) =>
       let
         val rs' = List.map (mapFst (P.map (fn FREE u => u | _ => raise Fail "infer/META: Did not expect bound symbol"))) rs
       in
         (X $# (rs', ms), tau)
       end
     | META _ => raise Fail "I am a number, not a free metavariable!!"

  and inferb (ABS (ssorts, vsorts, scope)) =
    let
      val Sc.\ ((us, xs), m) = Sc.outScope abtBindingSupport (ssorts, vsorts) scope
    in
      ((us, xs) \ m, ((ssorts, vsorts), sort m))
    end
  
  and outb abs = 
    #1 (inferb abs)

  fun check (view, tau) = 
    case view of 
       `x => makeVarTerm (FREE x, tau) NONE
     | theta $ args =>
       let
         val (vls, tau') = O.arity theta
         val _ = assertSortEq (tau, tau')

         val theta' = O.map (P.ret o FREE) theta
         val args' = ListPair.mapEq checkb (args, vls)
       in
         makeAppTerm (theta', args') NONE
       end
     | X $# (rs, ms) =>
       let
         val ssorts = List.map #2 rs
         val vsorts = List.map sort ms
         val rs' = List.map (fn (p, sigma) => (P.map FREE p, sigma) before (P.check sigma p; ())) rs
         fun chkInf (m, tau) = (assertSortEq (tau, sort m); m)
         val ms' = ListPair.mapEq chkInf (ms, vsorts)
       in
         makeMetaTerm ((FREE X, tau), rs', ms') NONE
       end

  val outb = #1 o inferb
  val valence = #2 o inferb
  val out = #1 o infer

  fun unbind (ABS (ssorts, vsorts, scope)) rs ms =
    let
      val rs' = ListPair.map (fn (r, sigma) => (P.check sigma r; P.map FREE r)) (rs, ssorts)
      val _ = ListPair.app (fn (m, tau) => assertSortEq (sort m, tau)) (ms, vsorts)
      val m = Sc.unsafeReadBody scope
    in
      instantiateAbt (0,0,0) (rs', ms, []) m
    end

  fun // (abs, (rs, ms)) =
    unbind abs rs ms

  fun $$ (theta, args) = 
    check (theta $ args, #2 (O.arity theta))

  fun locallyEq f = 
    fn (FREE x, FREE y) => f (x, y)
     | (BOUND i, BOUND j) => i = j
     | _ => false

  val rec eq = 
    fn (V (x, _) <: _, V (y, _) <: _) => locallyEq Var.eq (x, y)
     | (APP (theta1, args1) <: _, APP (theta2, args2) <: _) =>
       O.eq (locallyEq Sym.eq) (theta1, theta2)
         andalso ListPair.allEq eqAbs (args1, args2)
     | (META ((X1, _), rs1, ms1) <: _, META ((X2, _), rs2, ms2) <: _) =>
       locallyEq Metavar.eq (X1, X2)
         andalso ListPair.allEq (fn ((r1, _), (r2, _)) => P.eq (locallyEq Sym.eq) (r1, r2)) (rs1, rs2)
         andalso ListPair.allEq eq (ms1, ms2)
     | _ => false

  and eqAbs = 
    fn (ABS (_, _, scope1), ABS (_, _, scope2)) =>
      Sc.eq eq (scope1, scope2)

  fun mapAbs f abs =
    let
      val ((us, xs) \ m, vl) = inferb abs
    in
      checkb ((us, xs) \ f m, vl)
    end

  fun abtToAbs m = 
    ABS ([],[], Sc.intoScope abtBindingSupport (Sc.\ (([],[]), m)))

  fun mapSubterms f m =
    let
      val (view, tau) = infer m
    in
      setAnnotation (getAnnotation m) (check (map f view, tau))
    end

  fun deepMapSubterms f m =
    mapSubterms (f o deepMapSubterms f) m

end