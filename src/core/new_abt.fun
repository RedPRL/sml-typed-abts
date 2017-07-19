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
    {symIdxBound: int,
     varIdxBound: int,
     freeVars: varctx,
     freeSyms: symctx,
     hasMetas: bool}

  type annotation = annotation
  type internal_annotation =
    {user: annotation option,
     system: system_annotation}

  fun systemAnnLub (ann1 : system_annotation, ann2 : system_annotation) : system_annotation =
    {symIdxBound = Int.max (#symIdxBound ann1, #symIdxBound ann2),
     varIdxBound = Int.max (#varIdxBound ann1, #varIdxBound ann2),
     freeVars = VarCtxUtil.union (#freeVars ann1, #freeVars ann2),
     freeSyms = SymCtxUtil.union (#freeSyms ann1, #freeSyms ann2),
     hasMetas = #hasMetas ann1 orelse #hasMetas ann2}

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
  and meta_term = (Metavar.t * sort) * (Sym.t locally P.term * psort) list * abt_internal annotated list

  fun locallyToString f = 
    fn FREE x => f x
     | BOUND i => "<" ^ Int.toString i ^ ">"

  fun prettyList f l c r xs = 
    case xs of 
       [] => ""
     | _ => l ^ ListSpine.pretty f c xs ^ r

  fun primVarToString xs = 
    fn FREE x => Var.toString x
     | BOUND i =>
          if i < List.length xs then 
            "!" ^ List.nth (xs, List.length xs - i - 1)
          else
            "%" ^ Int.toString i

  fun primSymToString us = 
    fn FREE u => Sym.toString u
     | BOUND i => 
          if i < List.length us then 
            "!" ^ List.nth (us, List.length us - i - 1)
          else
            "%" ^ Int.toString i


  fun primToString' (us, xs) =
    fn V (v, _) <: _ => primVarToString xs v
     | APP (theta, es) <: _ =>
         O.toString (primSymToString us) theta
           ^ prettyList (primToStringAbs' (us, xs)) "(" "; " ")" es

     | META ((X, tau), rs, ms) <: _ =>
         "#" ^ Metavar.toString X
           ^ prettyList (P.toString (primSymToString us) o #1) "{" ", " "}" rs
           ^ prettyList (primToString' (us, xs)) "[" ", " "]" ms

  and primToStringAbs' (us, xs) =
    fn ABS ([], [], m) => primToString' (us, xs) (Sc.unsafeReadBody m)
     | ABS (ssorts, vsorts, sc) => 
         let
           val Sc.\ ((us', xs'), body) = Sc.unsafeRead sc
         in
           prettyList (fn x => x) "{" ", " "}" us' ^ 
           prettyList (fn x => x) "[" ", " "]" xs' ^ 
           "." ^ primToString' (us @ us', xs @ xs') body
         end

    val primToString = primToString' ([],[])
    val primToStringAbs = primToStringAbs' ([],[])

  type metaenv = abs Metavar.Ctx.dict
  type varenv = abt Var.Ctx.dict
  type symenv = param Sym.Ctx.dict

  val sort =
    fn V (_, tau) <: _ => tau
     | APP (theta, _) <: _ => #2 (O.arity theta)
     | META ((_, tau), _, _) <: _ => tau

  exception BoundVariable of string
  fun assertHasNotBoundVariable msg i (m <: _) = 
    case m of
       V (BOUND j, _) => if j >= i then raise BoundVariable msg else ()
     | APP (_, args) =>
       let
         fun onAbs (ABS (ssorts, vsorts, scope)) = 
           assertHasNotBoundVariable msg (i + List.length vsorts) (Sc.unsafeReadBody scope)
       in
         List.app onAbs args
       end
     | META (_, _, ms) => List.app (assertHasNotBoundVariable msg i) ms
     | _ => ()


  (* TODO: add diagnostics *)
  exception BadInstantiate


  type 'a binding_support = (abt, Sym.t locally P.term, 'a) Sc.binding_support

  fun scopeReadAnn scope =
    let
      val Sc.\ ((us, xs), body <: ann) = Sc.unsafeRead scope
      val {symIdxBound, varIdxBound, freeVars, freeSyms, hasMetas} = #system ann
      val symIdxBound' = symIdxBound - List.length us
      val varIdxBound' = varIdxBound - List.length xs
    in
      {user = #user ann,
       system = {symIdxBound = symIdxBound', varIdxBound = varIdxBound', freeSyms = freeSyms, freeVars = freeVars, hasMetas = hasMetas}}
    end

  fun makeVarTerm (var, tau) userAnn =
    case var of
       FREE x =>
         V (var, tau) <:
           {user = userAnn,
            system = {symIdxBound = 0,varIdxBound = 0, freeVars = Var.Ctx.singleton x tau, freeSyms = Sym.Ctx.empty, hasMetas = false}}

     | BOUND i =>
         V (var, tau) <:
           {user = userAnn,
            system = {symIdxBound = 0, varIdxBound = i + 1, freeVars = Var.Ctx.empty, freeSyms = Sym.Ctx.empty, hasMetas = false}}

  fun idxBoundForSyms support =
    List.foldl
      (fn ((FREE _,_), i) => i
        | ((BOUND i, _), j) => Int.max (i + 1, j))
      0
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
      val operatorAnn = {symIdxBound = symIdxBound, varIdxBound = 0, freeVars = Var.Ctx.empty, freeSyms = freeSyms, hasMetas = false}
      val systemAnn =
        List.foldl
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
      {symIdxBound = idxBoundForSyms support, varIdxBound = 0, freeVars = Var.Ctx.empty, freeSyms = freeSymsForSupport support, hasMetas = false}
    end

  (* For some reason, this is not setting the db-idx bounds properly in the system annotation *)
  fun makeMetaTerm (((X, tau), rs, ms) : meta_term) userAnn =
    let
      val metaSystemAnn = {symIdxBound = 0, varIdxBound = 0, freeVars = Var.Ctx.empty, freeSyms = Sym.Ctx.empty, hasMetas = true}

      val systemAnn =
        List.foldl
          (fn ((p, sigma), ann) => systemAnnLub (ann, paramSystemAnn (p, sigma)))
          metaSystemAnn
          rs

      val systemAnn =
        List.foldl
          (fn (_ <: termAnn, ann) => systemAnnLub (ann, #system termAnn))
          systemAnn
          ms
    in
      META ((X, tau), rs, ms) <: {user = userAnn, system = systemAnn}
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
      {debug: string,
       handleSym : int -> (symbol locally * psort) annotated -> 'p,
       handleVar : int -> var_term annotated -> 'a,
       shouldTraverse : int * int -> system_annotation -> bool}

    fun abtRec (alg : (symbol locally P.t, abt) abt_algebra) ixs (term <: (ann as {user, system})) : abt =
      if not (#shouldTraverse alg ixs system) then term <: ann else 
      case term of
         V (var, tau) => #handleVar alg (#2 ixs) ((var, tau) <: ann)
       | APP (theta, args) =>
         let
           val theta' = O.mapWithSort (fn (u, sigma) => #handleSym alg (#1 ixs) ((u, sigma) <: ann)) theta
           val args' = List.map (fn ABS (ssorts, vsorts, scope) => ABS (ssorts, vsorts, Sc.liftTraversal (abtRec alg) ixs scope)) args
         in
           makeAppTerm (theta', args') user
         end
       | META ((X, tau), rs, ms) =>
         let
           val rs' = List.map (fn (r, sigma) => (P.bind (fn u => #handleSym alg (#1 ixs) ((u, sigma) <: ann)) r, sigma)) rs
           val ms' = List.map (abtRec alg ixs) ms
         in
           makeMetaTerm ((X, tau), rs', ms') (#user ann)
         end
  

    fun abtAccum (acc : 'a monoid) (alg : ('a, 'a) abt_algebra) ixs (term <: (ann as {user, system})) : 'a =
      if not (#shouldTraverse alg ixs system) then #unit acc else 
      case term of
         V var => #handleVar alg (#2 ixs) (var <: ann)
       | APP (theta, args) =>
         let
           val support = O.support theta
           val memo = List.foldl (fn ((u, sigma), memo) => #mul acc (#handleSym alg (#1 ixs) ((u, sigma) <: ann), memo)) (#unit acc) support
         in
           List.foldl
             (fn (ABS (_, _, scope), memo) => #mul acc (Sc.unsafeReadBody (Sc.liftTraversal (abtAccum acc alg) ixs scope), memo))
             memo
             args
         end
       | META ((X, tau), rs, ms) =>
         let
           val memo =
             List.foldl
               (fn ((r, sigma), memo) =>
                  let
                    val support = P.check sigma r
                  in
                    List.foldl (fn ((u, sigma), memo) => #mul acc (#handleSym alg (#1 ixs) ((u, sigma) <: ann), memo)) memo support
                  end)
               (#unit acc)
               rs
         in
           List.foldl (fn (m, memo) => #mul acc (abtAccum acc alg ixs m, memo)) memo ms
         end

  in
 
    fun instantiateAbt (ixs : int * int) (rs, ms) : abt -> abt =
      let
        fun findInstantiation i items var =
          case var of
             FREE _ => NONE
           | BOUND i' =>
               if i' >= i andalso i' < i + List.length items then
                 SOME (List.nth (items, i' - i))
               else
                 NONE

        fun instantiateSym i ((sym, sigma) <: _) =
          case findInstantiation i rs sym of
             SOME r => (P.check sigma r; r)
           | NONE => P.ret sym

        fun instantiateVar j ((vt as (var, tau)) <: ann) =
          case findInstantiation j ms var of
             SOME m => if O.Ar.Vl.S.eq (sort m, tau) then m else raise BadInstantiate
           | NONE => V vt <: ann

        fun shouldTraverse (ixs : int * int) ({symIdxBound, varIdxBound,  ...} : system_annotation) =
          let
            (* TODO: check this logic. If there is no bound (sym, var, meta), then we have nothing to instantiate. does that make sense? *)
            val needSyms = #1 ixs < symIdxBound
            val needVars = #2 ixs < varIdxBound
          in
            (* TODO: this logic was incorect!*)
            needSyms orelse needVars
          end

        val alg =
          {debug = "instantiate",
           handleSym = instantiateSym,
           handleVar = instantiateVar,
           shouldTraverse = shouldTraverse}
      in
        abtRec alg ixs
      end

    fun abstractAbt ixs (us, xs) =
      let
        fun shouldTraverse ixs ({freeSyms, freeVars, hasMetas, ...} : system_annotation) =
          let
            val needSyms = case us of [] => false | _ => not (Sym.Ctx.isEmpty freeSyms)
            val needVars = case xs of [] => false | _ => not (Var.Ctx.isEmpty freeVars)
          in
            needSyms orelse needVars
          end

        fun abstractSym i =
          fn (sym as FREE u, _) <: _ => P.ret
             (case indexOfFirst (fn v => Sym.eq (u, v)) us of
                 NONE => sym
               | SOME i' => BOUND (i + i'))
           | (sym, _) <: _ => P.ret sym

        fun abstractVar j =
          fn (vt as (FREE x, tau)) <: ann =>
             (case indexOfFirst (fn y => Var.eq (x, y)) xs of
                 NONE => V vt <: ann
               | SOME j' => makeVarTerm (BOUND (j + j'), tau) (#user ann))
           | vt <: ann => V vt <: ann

        val alg =
          {debug = "abstract",
           handleSym = abstractSym,
           handleVar = abstractVar,
           shouldTraverse = shouldTraverse}
      in
        abtRec alg ixs
      end


   val abtBindingSupport : (abt, Sym.t locally P.t, abt) Sc.binding_support = 
    {abstract = abstractAbt,
     instantiate = instantiateAbt,
     freeVariable = fn (x, tau) => makeVarTerm (FREE x, tau) NONE,
     freeSymbol = fn u => P.ret (FREE u)}

     fun subst (srho: symenv, vrho : varenv) =
      let
        fun shouldTraverse _ ({freeVars, freeSyms, ...} : system_annotation) =
          let
            val needSyms = not (Sym.Ctx.isEmpty freeSyms orelse Sym.Ctx.isEmpty srho)
            val needVars = not (Var.Ctx.isEmpty freeVars orelse Var.Ctx.isEmpty vrho)
          in
            needSyms orelse needVars
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

        val alg =
          {debug = "subst",
           handleSym = handleSym,
           handleVar = handleVar,
           shouldTraverse = shouldTraverse}
      in
        abtRec alg (0,0)
      end

    fun varctx (_ <: {system = {freeVars, ...}, ...}) = 
      freeVars

    fun symctx (_ <: {system = {freeSyms, ...}, ...}) = 
      freeSyms

    val metactx : abt -> metactx =
      let
        fun aux metas (term <: {system = {hasMetas, ...}, ...}) = 
          if not hasMetas then metas else
          case term of 
             V _ => metas
           | APP (_, args) => auxArgs metas args
           | META ((X, tau), rs, ms) =>
             let
               val vl = ((List.map #2 rs, List.map sort ms), tau)
               val metas' = Metavar.Ctx.insert metas X vl
             in
               auxTerms metas' ms
             end
        and auxArgs metas = List.foldl (fn (abs, metas) => auxAbs metas abs) metas
        and auxAbs metas (ABS (_, _, scope)) = aux metas (Sc.unsafeReadBody scope)
        and auxTerms metas = List.foldl (fn (term, metas) => aux metas term) metas
      in
        aux Metavar.Ctx.empty
      end

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
          {debug = "symOccurrences",
           handleSym = handleSym,
           handleVar = fn _ => fn _ => Sym.Ctx.empty,
           shouldTraverse = fn _ => fn ({freeSyms, ...} : system_annotation) => not (Sym.Ctx.isEmpty freeSyms)}
      in
        abtAccum monoid alg (0,0)
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
          {debug = "varOccurrences",
           handleSym = fn _ => fn _ => Var.Ctx.empty,
           handleVar = handleVar,
           shouldTraverse = fn _ => fn ({freeVars, ...} : system_annotation) => not (Var.Ctx.isEmpty freeVars)}
      in 
        abtAccum monoid alg (0,0)
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
          {debug = "renameVars",
           handleSym = fn _ => fn (sym, tau) <: ann => P.ret sym,
           handleVar = handleVar,
           shouldTraverse = fn _ => fn ({freeVars, ...} : system_annotation) => not (Var.Ctx.isEmpty freeVars)}
      in
        abtRec alg (0,0)
      end
  end

  exception BadSubstMetaenv of {metaenv : metaenv, term : abt, description : string}

  fun substVarenv vrho =
    subst (Sym.Ctx.empty, vrho)

  fun substSymenv srho =
    subst (srho, Var.Ctx.empty)


  fun substVar (m, x) =
    substVarenv (Var.Ctx.singleton x m)

  fun substSymbol (r, u) =
    substSymenv (Sym.Ctx.singleton u r)


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
      val tau' = sort m
      val syms = symctx m
      val vars = varctx m
    in
      assertSortEq (tau, tau');
      ListPair.appEq (fn (u, sigma) => assertPSortEq (sigma, Option.getOpt (Sym.Ctx.find syms u, sigma))) (us, ssorts);
      ListPair.appEq (fn (x, tau) => assertSortEq (tau, Option.getOpt (Var.Ctx.find vars x, tau))) (xs, vsorts);
      ABS (ssorts, vsorts, Sc.intoScope abtBindingSupport (Sc.\ ((us, xs), m)))
    end

  fun infer (term <: ann) =
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
     | META ((X, tau), rs, ms) =>
       let
         val rs' = List.map (mapFst (P.map (fn FREE u => u | _ => raise Fail "infer/META: Did not expect bound symbol"))) rs
       in
         (X $# (rs', ms), tau)
       end

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
         makeMetaTerm ((X, tau), rs', ms') NONE
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
      instantiateAbt (0,0) (rs', ms) m
    end

  fun // (abs, (rs, ms)) =
    unbind abs rs ms

  infix //

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
       Metavar.eq (X1, X2)
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

  fun substMetaenv mrho (term as _ <: {system = {hasMetas, ...}, ...}) =
    if not hasMetas then term else
    case infer term of
       (`_, _) => term
     | (theta $ args, tau) =>
       let
         fun aux ((us, xs) \ m) = (us,xs) \ substMetaenv mrho m
         val args' = List.map aux args
       in
         check (theta $ args', tau)
       end
     | (X $# (rs, ms), tau) =>
       let
         val ms' = List.map (substMetaenv mrho) ms
       in
         case Metavar.Ctx.find mrho X of 
            NONE => check (X $# (rs, ms'), tau)
          | SOME abs => abs // (List.map #1 rs, ms')
       end

  fun substMetavar (scope, X) =
    substMetaenv (Metavar.Ctx.singleton X scope)

end