functor NewAbt
  (structure Sym : ABT_SYMBOL
   structure Var : ABT_SYMBOL
   structure Metavar : ABT_SYMBOL
   structure O : ABT_OPERATOR where type 'a Ar.Vl.Sp.t = 'a list
   type user_annotation) : ABT =
struct

  structure Sym = Sym and Var = Var and Metavar = Metavar and O = O
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
     hasFreeVars: bool,
     hasFreeSyms: bool,
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
     hasFreeVars = #hasFreeVars ann1 orelse #hasFreeVars ann2,
     hasFreeSyms = #hasFreeSyms ann1 orelse #hasFreeSyms ann2,
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
      val {symIdxBound, varIdxBound, metaIdxBound, hasFreeVars, hasFreeSyms, hasFreeMetas} = #system ann
      val symIdxBound' = Option.map (fn i => i - List.length us) symIdxBound 
      val varIdxBound' = Option.map (fn i => i - List.length xs) varIdxBound
    in
      {user = #user ann,
       system = {symIdxBound = symIdxBound', varIdxBound = varIdxBound', metaIdxBound = metaIdxBound, hasFreeSyms = hasFreeSyms, hasFreeVars = hasFreeVars, hasFreeMetas = hasFreeMetas}}
    end

  fun makeVarTerm (var, tau) userAnn = 
    case var of 
       FREE x =>
         V (var, tau) <:
           {user = userAnn,
            system =
              {symIdxBound = NONE, varIdxBound = NONE, metaIdxBound = NONE, hasFreeVars = true, hasFreeSyms = false, hasFreeMetas = false}}

     | BOUND i =>
         V (var, tau) <:
           {user = userAnn,
            system = {symIdxBound = NONE, varIdxBound = SOME (i + 1), metaIdxBound = NONE, hasFreeVars = false, hasFreeSyms = false, hasFreeMetas = false}}

  fun idxBoundForSyms support = 
    List.foldr
      (fn ((FREE _,_), oidx) => oidx
        | ((BOUND i, _), NONE) => SOME (i + 1)
        | ((BOUND i, _), SOME j) => SOME (Int.max (i, j)))
      NONE
      support

  fun supportContainsFreeSyms support = 
    Option.isSome (List.find (fn (FREE _, _) => true | _ => false) support)    

  fun makeAppTerm (theta, scopes) userAnn =
    let
      val support = O.support theta
      val hasFreeSyms = supportContainsFreeSyms support
      val symIdxBound = idxBoundForSyms support
      val operatorAnn = {symIdxBound = symIdxBound, varIdxBound = NONE, metaIdxBound = NONE, hasFreeVars = false, hasFreeSyms = hasFreeSyms, hasFreeMetas = false}

      val systemAnn =
        List.foldr
          (fn (scope, ann) => systemAnnLub (ann, #system (scopeReadAnn scope)))
          operatorAnn
          scopes
    in
      APP (theta, scopes) <: {user = userAnn, system = systemAnn}
    end

  val paramSystemAnn = 
    fn P.VAR (FREE x) => {symIdxBound = NONE, varIdxBound = NONE, metaIdxBound = NONE, hasFreeVars = false, hasFreeSyms = true, hasFreeMetas = false}
     | P.VAR (BOUND i) => {symIdxBound = SOME (i + 1), varIdxBound = NONE, metaIdxBound = NONE, hasFreeVars = false, hasFreeSyms = false, hasFreeMetas = false}
     | P.APP t => 
        let
          val support = P.freeVars t
        in
          {symIdxBound = idxBoundForSyms support, varIdxBound = NONE, metaIdxBound = NONE, hasFreeVars = false, hasFreeSyms = supportContainsFreeSyms support, hasFreeMetas = false}
        end
    
  fun makeMetaTerm (((meta, tau), rs, ms) : meta_term) userAnn =
    let
      val (metaIdxBound, hasFreeMetas) = case meta of FREE _ => (NONE, true) | BOUND j => (SOME (j + 1), false)
      val metaSystemAnn = {symIdxBound = NONE, varIdxBound = NONE, metaIdxBound = metaIdxBound, hasFreeVars = false, hasFreeSyms = false, hasFreeMetas = hasFreeMetas}
      val systemAnn = 
        List.foldr 
          (fn ((p, _), ann) => systemAnnLub (ann, paramSystemAnn p))
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

    fun abstractSym i us =
      fn FREE u =>
         (case indexOfFirst (fn v => Sym.eq (u, v)) us of 
             NONE => FREE u
           | SOME k => BOUND (i + k))
       | BOUND k => BOUND k

    (* TODO: sort checking? *)
    fun instantiateSym i rs sym =
      case findInstantiation i rs sym of 
         SOME r => r
       | NONE => P.ret sym

  in
    fun abtBindingSupport () : abt binding_support = 
      {abstract = abstractAbt,
       instantiate = instantiateAbt,
       freeVariable = fn (x, tau) => makeVarTerm (FREE x, tau) NONE,
       freeSymbol = P.ret o FREE}

    and instantiateAbt (i, j, k) (rs, ms, scopes) (term <: ann) =
      let
        val {symIdxBound, varIdxBound, metaIdxBound, ...} = #system ann
        (* if all the following things hold, then there would be no variable or symbol to instantiate *)
        val noNeedSyms = case symIdxBound of SOME i' => i >= i' | NONE => false
        val noNeedVars = case varIdxBound of SOME j' => j >= j' | NONE => false
        val noNeedMetas = case metaIdxBound of SOME k' => k >= k' | NONE => false
      in
        if noNeedSyms andalso noNeedVars andalso noNeedMetas then term <: ann else
        case term of
           V (var, tau) => 
           (case findInstantiation j ms var of 
               SOME m => if O.Ar.Vl.S.eq (sort m, tau) then m else raise BadInstantiate
             | NONE => V (var, tau) <: ann)
         | APP (theta, args) =>
           let
             val scopeBindingSupport = Sc.scopeBindingSupport (abtBindingSupport ())
             val theta' = O.map (instantiateSym i rs) theta
             val args' = List.map (#instantiate scopeBindingSupport (i, j, k) (rs, ms, scopes)) args
           in
             makeAppTerm (theta', args') (#user ann)
           end
         | META ((X, tau), rsX, msX) =>
           let
             val rsX' = List.map (mapFst (P.bind (instantiateSym i rs))) rsX
             val msX' = List.map (instantiateAbt (i, j, k) (rs, ms, scopes)) msX
           in
             case findInstantiation k scopes X of 
                SOME scope => instantiateAbt (i, j, k) (List.map #1 rsX', msX', scopes) (Sc.unsafeReadBody scope)
              | NONE => makeMetaTerm ((X, tau), rsX', msX') (#user ann)
           end
      end

    and abstractAbt (i, j, k) (us, xs, Xs) (term <: ann) =
      let
        val {hasFreeSyms, hasFreeVars, hasFreeMetas, ...} = #system ann
        val noNeedSyms = case us of [] => true | _ => not hasFreeSyms
        val noNeedVars = case xs of [] => true | _ => not hasFreeVars
        val noNeedMetas = case Xs of [] => true | _ => not hasFreeMetas
      in
        if noNeedSyms andalso noNeedVars andalso noNeedMetas then term <: ann else 
        case term of
           V (BOUND _, _) => term <: ann
         | V (FREE x, tau) =>
             (case indexOfFirst (fn y => Var.eq (x, y)) xs of 
                 NONE => makeVarTerm (FREE x, tau) (#user ann)
               | SOME j' => makeVarTerm (BOUND (j + j'), tau) (#user ann))
         | APP (theta, scopes) =>
           let
             val scopeBindingSupport = Sc.scopeBindingSupport (abtBindingSupport ())
             val theta' = O.map (P.ret o abstractSym i us) theta
             val scopes' = List.map (#abstract scopeBindingSupport (i, j, k) (us, xs, Xs)) scopes
           in
             makeAppTerm (theta', scopes') (#user ann)
           end
         | META ((FREE X, tau), rs, ms) =>
             let
               val meta = 
                 case indexOfFirst (fn Y => Metavar.eq (X, Y)) Xs of 
                    NONE => FREE X
                  | SOME k' => BOUND (k + k')
               val rs' = List.map (mapFst (P.map (abstractSym i us))) rs
               val ms' = List.map (abstractAbt (i, j, k) (us, xs, Xs)) ms
             in
               makeMetaTerm ((meta, tau), rs', ms') (#user ann)
             end
      end
  end


  exception BadSubstMetaenv of {metaenv : metaenv, term : abt, description : string}

  exception todo
  fun ?e = raise e

  fun varctx _ = ?todo
  fun symctx _ = ?todo
  fun metactx _ = ?todo

  fun symOccurrences _ = ?todo
  fun varOccurrences _ = ?todo


  (* The following could be improved by fusing the abstract and instantiate traversals. Maybe there
     is some way to do this using a CPS'd version of those functions? *)
  fun substVar (m, x) =
    instantiateAbt (0,0,0) ([], [m], [])
      o abstractAbt (0,0,0) ([], [x], [])

  fun substSymbol (r, u) =
    instantiateAbt (0,0,0) ([P.map FREE r], [], [])
      o abstractAbt (0,0,0) ([u], [], [])

  fun substMetavar (scope, X) =
    instantiateAbt (0,0,0) ([], [], [scope])
      o abstractAbt (0,0,0) ([], [], [X])

  fun substVarenv _ = ?todo
  fun substSymenv _ = ?todo
  fun substMetaenv _ = ?todo

  fun renameVars _ = ?todo
  
  fun annotate _ = ?todo
  fun getAnnotation _ = ?todo
  fun setAnnotation _ = ?todo
  fun clearAnnotation _ = ?todo


  fun unbind _ = ?todo
  fun // _ = ?todo
  fun $$ _ = ?todo

  fun infer _ = ?todo
  fun check _ = ?todo
  fun out _ = ?todo
  fun checkb _ = ?todo
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