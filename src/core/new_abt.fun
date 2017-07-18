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

    type traverse_kit = 
      {handleSym : int -> symbol locally -> symbol locally P.t,
       handleVar : int -> var_term annotated -> abt,
       handleMeta : int * int * int -> meta_term annotated -> abt,
       shouldTraverse : int * int * int -> system_annotation -> bool}

    fun traverseAbt (kit : traverse_kit) (i, j, k) (term <: (ann as {user, system})) : abt = 
      if not (#shouldTraverse kit (i, j, k) system) then term <: ann else
      case term of 
         V (var, tau) => #handleVar kit j ((var, tau) <: ann)
       | APP (theta, args) =>
         let
           val theta' = O.map (#handleSym kit i) theta
           val args' = List.map (Sc.liftTraversal (traverseAbt kit) (i, j, k)) args
         in
           makeAppTerm (theta', args') user
         end
       | META ((X, tau), rs, ms) => 
         let
           val rs' = List.map (mapFst (P.bind (#handleSym kit i))) rs
           val ms' = List.map (traverseAbt kit (i, j, k)) ms
         in
           #handleMeta kit (i, j, k) (((X, tau), rs', ms') <: ann)
         end

  in
    fun instantiateAbt (i, j, k) (rs, ms, scopes) =
      let
        (* TODO: sort checking? *)
        fun instantiateSym i rs sym =
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

        val kit = 
          {handleSym = fn i => instantiateSym i rs,
           handleVar = fn j => instantiateVar j ms,
           handleMeta = instantiateMeta,
           shouldTraverse = shouldTraverse}
      in
        traverseAbt kit (i, j, k)
      end

    and abstractAbt (i, j, k) (us, xs, Xs) =
      let
        fun shouldTraverse (i, j, k) ({hasFreeSyms, hasFreeVars, hasFreeMetas, ...} : system_annotation) = 
          let
            val needSyms = case us of [] => false | _ => hasFreeSyms
            val needVars = case xs of [] => false | _ => hasFreeVars
            val needMetas = case Xs of [] => true | _ => hasFreeMetas
          in
            needSyms orelse needVars orelse needMetas
          end

        fun abstractSym i us =
          fn FREE u =>
             (case indexOfFirst (fn v => Sym.eq (u, v)) us of 
                 NONE => FREE u
               | SOME i' => BOUND (i + i'))
           | BOUND i' => BOUND i'

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

        val kit =
          {handleSym = fn i => P.ret o abstractSym i us,
           handleVar = fn j => abstractVar j xs,
           handleMeta = abstractMeta,
           shouldTraverse = shouldTraverse}
      in
        traverseAbt kit (i, j, k)
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