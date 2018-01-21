functor Abt
  (structure Var : ABT_SYMBOL
   structure Metavar : ABT_SYMBOL
   structure O : ABT_OPERATOR
   type annotation) : ABT =
struct
  exception todo
  fun ?e = raise e

  structure Var = Var and Metavar = Metavar and O = O

  structure S = O.Ar.Vl.S and Valence = O.Ar.Vl
  structure MetaCtxUtil = ContextUtil (structure Ctx = Metavar.Ctx and Elem = Valence)
  structure VarCtxUtil = ContextUtil (structure Ctx = Var.Ctx and Elem = S)

  type sort = O.Ar.Vl.S.t

  structure Sc = LnScope (structure Var = Var and Metavar = Metavar type sort = sort)
  datatype 'a locally =
     FREE of 'a
   | BOUND of int

  type variable = Var.t
  type metavariable = Metavar.t
  type operator = O.t
  type valence = O.Ar.valence
  type varctx = sort Var.Ctx.dict
  type metactx = valence Metavar.Ctx.dict

  exception SortError of {annotation: annotation option, description: string}

  structure Views = AbtViews
  open Views

  type 'a view = (variable, metavariable, operator, 'a) termf
  type 'a bview = (variable, 'a) bindf
  type 'a appview = (variable, operator, 'a) appf

  infixr 5 \
  infix 5 $ $#

  type system_annotation =
    {varIdxBound: int,
     freeVars: varctx,
     hasMetas: bool}

  type annotation = annotation
  type internal_annotation =
    {user: annotation option,
     system: system_annotation}

  fun systemAnnLub (ann1 : system_annotation, ann2 : system_annotation) : system_annotation =
    {varIdxBound = Int.max (#varIdxBound ann1, #varIdxBound ann2),
     freeVars = VarCtxUtil.union (#freeVars ann1, #freeVars ann2),
     hasMetas = #hasMetas ann1 orelse #hasMetas ann2}

  datatype 'a annotated = <: of 'a * internal_annotation
  infix <:

  datatype abt_internal =
     V of var_term
   | APP of app_term
   | META of meta_term
  and abs = ABS of sort list * abt Sc.scope
  withtype abt = abt_internal annotated
  and var_term = Var.t locally * sort
  and app_term = O.t * abs list
  and meta_term = (Metavar.t * sort) * abt_internal annotated list

  fun locallyToString f = 
    fn FREE x => f x
     | BOUND i => "<" ^ Int.toString i ^ ">"

  fun prettyList f l c r xs = 
    case xs of 
       [] => ""
     | _ => l ^ ListUtil.joinWith f c xs ^ r

  fun primVarToString xs = 
    fn FREE x => Var.toString x
     | BOUND i =>
          if i < List.length xs then 
            "!" ^ 
              (case List.nth (xs, List.length xs - i - 1) of 
                  SOME s => s
                | NONE => "?")
          else
            "%" ^ Int.toString i

  fun primToString' xs =
    fn V (v, _) <: _ => primVarToString xs v
     | APP (theta, es) <: _ =>
         O.toString theta
           ^ prettyList (primToStringAbs' xs) "(" "; " ")" es

     | META ((X, tau), ms) <: _ =>
         "#" ^ Metavar.toString X
           ^ prettyList (primToString' xs) "[" ", " "]" ms

  and primToStringAbs' xs =
    fn ABS ([], m) => primToString' xs (Sc.unsafeReadBody m)
     | ABS (vsorts, sc) => 
         let
           val Sc.\ (xs', body) = Sc.unsafeRead sc
         in
           prettyList (fn SOME x => x | NONE => "?") "[" ", " "]" xs' ^ 
           "." ^ primToString' (xs @ xs') body
         end

  val primToString = primToString' []
  val primToStringAbs = primToStringAbs' []

  fun assertSortEq ann (sigma, tau) =
    if S.eq (sigma, tau) then () else
      raise SortError
        {annotation = ann,
         description = "Sort Error: expected " ^ S.toString sigma ^ ", but got " ^ S.toString tau}

  type metaenv = abs Metavar.Ctx.dict
  type varenv = abt Var.Ctx.dict

  val sort =
    fn V (_, tau) <: _ => tau
     | APP (theta, _) <: _ => #2 (O.arity theta)
     | META ((_, tau), _) <: _ => tau

  type 'a binding_support = (abt, 'a) Sc.binding_support

  fun scopeReadAnn scope =
    let
      val Sc.\ (xs, body <: ann) = Sc.unsafeRead scope
      val {varIdxBound, freeVars, hasMetas} = #system ann
      val varIdxBound' = varIdxBound - List.length xs
    in
      {user = #user ann,
       system = {varIdxBound = varIdxBound', freeVars = freeVars, hasMetas = hasMetas}}
    end

  fun makeVarTerm (var, tau) userAnn =
    case var of
       FREE x =>
         V (var, tau) <:
           {user = userAnn,
            system = {varIdxBound = 0, freeVars = Var.Ctx.singleton x tau, hasMetas = false}}

     | BOUND i =>
         V (var, tau) <:
           {user = userAnn,
            system = {varIdxBound = i + 1, freeVars = Var.Ctx.empty, hasMetas = false}}

  fun makeAppTerm (theta, scopes) userAnn =
    let
      val operatorAnn = {varIdxBound = 0, freeVars = Var.Ctx.empty, hasMetas = false}
      val systemAnn =
        List.foldl
          (fn (ABS (_, scope), ann) => systemAnnLub (ann, #system (scopeReadAnn scope)))
          operatorAnn
          scopes
    in
      APP (theta, scopes) <: {user = userAnn, system = systemAnn}
    end

  fun makeMetaTerm (((X, tau), ms) : meta_term) userAnn =
    let
      val metaSystemAnn = {varIdxBound = 0, freeVars = Var.Ctx.empty, hasMetas = true}
      val systemAnn =
        List.foldl
          (fn (_ <: termAnn, ann) => systemAnnLub (ann, #system termAnn))
          metaSystemAnn
          ms
    in
      META ((X, tau), ms) <: {user = userAnn, system = systemAnn}
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

    type ('meta, 'a) abt_algebra =
      {debug: string,
       handleVar : int -> var_term annotated -> 'a,
       handleMeta : metavariable * valence -> 'meta,
       shouldTraverse : int -> system_annotation -> bool}

    fun abtRec (alg : (metavariable, abt) abt_algebra) ix (term <: (ann as {user, system})) : abt =
      if not (#shouldTraverse alg ix system) then term <: ann else 
      case term of
         V (var, tau) => #handleVar alg ix ((var, tau) <: ann)
       | APP (theta, args) =>
         let
           val args' = List.map (fn ABS (vsorts, scope) => ABS (vsorts, Sc.liftTraversal (abtRec alg) ix scope)) args
         in
           makeAppTerm (theta, args') user
         end
       | META ((X, tau), ms) =>
         let
           val ms' = List.map (abtRec alg ix) ms
           val vl = (List.map sort ms', tau)
         in
           makeMetaTerm ((#handleMeta alg (X, vl), tau), ms') (#user ann)
         end
  

    fun abtAccum (acc : 'a monoid) (alg : ('a, 'a) abt_algebra) ix (term <: (ann as {user, system})) : 'a =
      if not (#shouldTraverse alg ix system) then #unit acc else 
      case term of
         V var => #handleVar alg ix (var <: ann)
       | APP (theta, args) =>
           List.foldl
             (fn (ABS (_, scope), memo) => #mul acc (Sc.unsafeReadBody (Sc.liftTraversal (abtAccum acc alg) ix scope), memo))
             (#unit acc)
             args
       | META ((X, tau), ms) =>
           List.foldl (fn (m, memo) => #mul acc (abtAccum acc alg ix m, memo)) (#unit acc) ms

  in
 
    fun instantiateAbt (ix : int) ms : abt -> abt =
      let
        fun findInstantiation i items var =
          case var of
             FREE _ => NONE
           | BOUND i' =>
               if i' >= i andalso i' < i + List.length items then
                 SOME (List.nth (items, i' - i))
               else
                 NONE

        fun instantiateVar j ((vt as (var, tau)) <: ann) =
          case findInstantiation j ms var of
             SOME m => (assertSortEq (#user ann) (tau, sort m); m)
           | NONE => V vt <: ann

        fun shouldTraverse ix ({varIdxBound,  ...} : system_annotation) =
          ix < varIdxBound

        val alg =
          {debug = "instantiate",
           handleVar = instantiateVar,
           handleMeta = fn (X, _) => X,
           shouldTraverse = shouldTraverse}
      in
        abtRec alg ix
      end

    fun abstractAbt (ix : int)  xs =
      let
        fun shouldTraverse ix ({freeVars, hasMetas, ...} : system_annotation) =
          case xs of [] => false | _ => not (Var.Ctx.isEmpty freeVars)

        fun abstractVar j =
          fn (vt as (FREE x, tau)) <: ann =>
             (case indexOfFirst (fn y => Var.eq (x, y)) xs of
                 NONE => V vt <: ann
               | SOME j' => makeVarTerm (BOUND (j + j'), tau) (#user ann))
           | vt <: ann => V vt <: ann

        val alg =
          {debug = "abstract",
           handleVar = abstractVar,
           handleMeta = fn (X, _) => X,
           shouldTraverse = shouldTraverse}
      in
        abtRec alg ix
      end


     val abtBindingSupport : (abt, abt) Sc.binding_support = 
       {abstract = abstractAbt,
        instantiate = instantiateAbt,
        freeVariable = fn (x, tau) => makeVarTerm (FREE x, tau) NONE}


    fun varctx (_ <: {system = {freeVars, ...}, ...}) = 
      freeVars

    val metactx : abt -> metactx = 
      let
        val monoid : (metactx -> metactx) monoid =
          {unit = fn ctx => ctx,
           mul = op o}

        val alg =
          {debug = "varOccurrences",
           handleVar = fn _ => fn _ => #unit monoid,
           handleMeta = fn (X, vl) => fn ctx => Metavar.Ctx.insert ctx X vl,
           shouldTraverse = fn _ => fn ({hasMetas, ...} : system_annotation) => hasMetas}
      in
        fn tm => abtAccum monoid alg 0 tm Metavar.Ctx.empty
      end

    val varOccurrences = 
      let
        type occurrences = annotation list Var.Ctx.dict
        val monoid : (occurrences -> occurrences) monoid =
          {unit = fn occs => occs,
           mul = op o}

        fun handleVar _ ((var, _) <: {user, system}) =
          case (var, user) of 
             (FREE x, SOME ann) => (fn occs => #3 (Var.Ctx.operate occs x (fn _ => [ann]) (fn anns => ann :: anns)))
           | _ => #unit monoid

        val alg =
          {debug = "varOccurrences",
           handleVar = handleVar,
           handleMeta = fn _ => #unit monoid,
           shouldTraverse = fn _ => fn ({freeVars, ...} : system_annotation) => not (Var.Ctx.isEmpty freeVars)}
      in
        fn tm => abtAccum monoid alg 0 tm Var.Ctx.empty
      end

    fun renameVars vrho = 
      let
        fun handleVar _ ((vt as (var, tau)) <: ann) = 
          case var of
             FREE x =>
             (case Var.Ctx.find vrho x of 
                 SOME y => makeVarTerm (FREE y, tau) (#user ann)
               | NONE => V vt <: ann)
           | _ => V vt <: ann

        val alg =
          {debug = "renameVars",
           handleVar = handleVar,
           handleMeta = fn (X, _) => X,
           shouldTraverse = fn _ => fn ({freeVars, ...} : system_annotation) => not (Var.Ctx.isEmpty freeVars)}
      in
        abtRec alg 0
      end

      fun renameMetavars mrho =
        let
          fun handleMeta (X, _) = 
            case Metavar.Ctx.find mrho X of
               SOME Y => Y
             | NONE => X

          val alg =
            {debug = "renameMetavars",
             handleVar = fn _ => fn vt <: ann => V vt <: ann,
             handleMeta = handleMeta,
             shouldTraverse = fn _ => fn ({hasMetas, ...} : system_annotation) => hasMetas}
        in
          abtRec alg 0
        end

      fun substVarenv (vrho : varenv) =
      let
        fun shouldTraverse _ ({freeVars, ...} : system_annotation) =
          not (Var.Ctx.isEmpty freeVars orelse Var.Ctx.isEmpty vrho)

        fun handleVar _ ((vt as (var, tau)) <: ann) =
          case var of
              FREE x =>
              (case Var.Ctx.find vrho x of
                  NONE => V vt <: ann
                | SOME m => m)
            | BOUND _ => V vt <: ann

        val alg =
          {debug = "subst",
            handleVar = handleVar,
            handleMeta = fn (X, _) => X,
            shouldTraverse = shouldTraverse}
      in
        abtRec alg 0
      end
  end

  fun substVar (m, x) =
    substVarenv (Var.Ctx.singleton x m)

  fun annotate ann (m <: {system, ...}) = m <: {user = SOME ann, system = system}
  fun getAnnotation (_ <: {user, ...}) = user
  fun setAnnotation ann (m <: {system, ...}) = m <: {user = ann, system = system}
  fun clearAnnotation (m <: {system, ...}) = m <: {user = NONE, system = system}

  fun metavar (X, (taus, tau)) = 
    let
      fun aux f i names results sorts = 
        case sorts of 
           [] => (List.rev names, List.rev results)
         | sort::sorts => 
           let
             val r = f (i, sort)
           in
             aux f (i + 1) (SOME ("?" ^ Int.toString i) :: names) (r :: results) sorts
           end

      val (xs, ms) = aux (fn (i, tau) => makeVarTerm (BOUND i, tau) NONE) 0 [] [] taus
      val body = makeMetaTerm ((X, tau), ms) NONE
      val scope = Sc.\ (xs, body)
    in
      ABS (taus, Sc.unsafeMakeScope scope)
    end

  fun checkb (xs \ m, (vsorts, tau)) : abs =
    let
      val tau' = sort m
      val vars = varctx m
    in
      assertSortEq (getAnnotation m) (tau, tau');
      ListPair.appEq (fn (x, tau) => assertSortEq (getAnnotation m) (tau, Option.getOpt (Var.Ctx.find vars x, tau))) (xs, vsorts);
      ABS (vsorts, Sc.intoScope abtBindingSupport (Sc.\ (xs, m)))
    end

  fun infer (term <: ann) =
    case term of 
       V (FREE x, tau) => (`x, tau)
     | V _ => raise Fail "I am a number, not a free variable!!"
     | APP (theta, args) =>
       let
         val (vls, tau) = O.arity theta
         val args' = List.map outb args
       in
         (theta $ args', tau)
       end
     | META ((X, tau), ms) => (X $# ms, tau)

  and inferb (ABS (vsorts, scope)) =
    let
      val Sc.\ (xs, m) = Sc.outScope abtBindingSupport vsorts scope
    in
      (xs \ m, (vsorts, sort m))
    end
  
  and outb abs = 
    #1 (inferb abs)

  fun check (view, tau) = 
    case view of 
       `x => makeVarTerm (FREE x, tau) NONE
     | theta $ args =>
       let
         val (vls, tau') = O.arity theta
         val _ = assertSortEq NONE (tau, tau')
         val args' = ListPair.mapEq checkb (args, vls)
       in
         makeAppTerm (theta, args') NONE
       end
     | X $# ms =>
       let
         val vsorts = List.map sort ms
         fun chkInf (m, tau) = (assertSortEq (getAnnotation m) (tau, sort m); m)
         val ms' = ListPair.mapEq chkInf (ms, vsorts)
       in
         makeMetaTerm ((X, tau), ms') NONE
       end

  val outb = #1 o inferb
  val valence = #2 o inferb
  val out = #1 o infer

  fun unbind (ABS (vsorts, scope)) ms =
    let
      val _ = ListPair.app (fn (m, tau) => assertSortEq (getAnnotation m) (tau, sort m)) (ms, vsorts)
      val m = Sc.unsafeReadBody scope
    in
      instantiateAbt 0 ms m
    end

  fun // (abs,  ms) =
    unbind abs ms

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
       O.eq (theta1, theta2)
         andalso ListPair.allEq eqAbs (args1, args2)
     | (META ((X1, _), ms1) <: _, META ((X2, _), ms2) <: _) =>
       Metavar.eq (X1, X2)
         andalso ListPair.allEq eq (ms1, ms2)
     | _ => false

  and eqAbs = 
    fn (ABS (_, scope1), ABS (_, scope2)) =>
      Sc.eq eq (scope1, scope2)

  fun mapAbs f abs =
    let
      val (xs \ m, vl) = inferb abs
    in
      checkb (xs \ f m, vl)
    end

  fun abtToAbs m = 
    ABS ([], Sc.intoScope abtBindingSupport (Sc.\ ([], m)))


  fun inheritAnnotation t1 t2 =
    case getAnnotation t2 of
        NONE => setAnnotation (getAnnotation t1) t2
      | _ => t2

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
         fun aux (xs \ m) = xs \ substMetaenv mrho m
         val args' = List.map aux args
       in
         inheritAnnotation term (check (theta $ args', tau))
       end
     | (X $# ms, tau) =>
       let
         val ms' = List.map (substMetaenv mrho) ms
       in
         case Metavar.Ctx.find mrho X of 
            NONE => inheritAnnotation term (check (X $# ms', tau))
          | SOME abs => abs // ms'
       end

  fun substMetavar (scope, X) =
    substMetaenv (Metavar.Ctx.singleton X scope)

end

functor SimpleAbt (O : ABT_OPERATOR) =
  Abt (structure Sym = AbtSymbol ()
       structure Var = AbtSymbol ()
       structure Metavar = AbtSymbol ()
       structure O = O
       type annotation = unit)
