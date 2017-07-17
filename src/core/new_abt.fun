functor NewAbt
  (structure Sym : ABT_SYMBOL
   structure Var : ABT_SYMBOL
   structure Metavar : ABT_SYMBOL
   structure O : ABT_OPERATOR
   type user_annotation) =
struct
  type sort = O.Ar.Vl.S.t
  type psort = O.Ar.Vl.PS.t

  structure P = O.P
  type param = Sym.t P.term

  structure Sc = LnScope (structure Sym = Sym and Var = Var and Metavar = Metavar type psort = psort type sort = sort)
  datatype 'a locally =
     FREE of 'a
   | BOUND of int

  type varctx = sort Var.Ctx.dict
  type symctx = psort Sym.Ctx.dict

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

  datatype abt_internal = 
     V of var_term
   | APP of app_term
   | META of meta_term
  and abt = <: of abt_internal * annotation
  withtype var_term = Var.t locally * sort
  and app_term = Sym.t locally O.t * abt Sc.scope list
  and meta_term = (Metavar.t locally * sort) * (Sym.t locally P.term * psort) list * abt list

  infix <:

  type 'a binding_support = (abt, Sym.t locally P.term, 'a) Sc.binding_support

  fun scopeReadAnn scope = 
    let
      val Sc.\ ((us, xs), body <: ann) = Sc.unsafeRead scope
      val {symIdxBound, varIdxBound, metaIdxBound, hasFreeVars, hasFreeSyms, hasFreeMetas} = #system ann
      val symIdxBound' = Option.map (fn i => i - List.length us) symIdxBound 
      val varIdxBound' = Option.map (fn i => i - List.length xs) varIdxBound
    in
      {user = #user ann,
       system =
         {symIdxBound = symIdxBound',
          varIdxBound = varIdxBound',
          metaIdxBound = metaIdxBound,
          hasFreeSyms = hasFreeSyms,
          hasFreeVars = hasFreeVars,
          hasFreeMetas = hasFreeMetas}}
    end

  fun makeVarTerm (var, tau) userAnn = 
    case var of 
       FREE x =>
         V (var, tau) <:
           {user = userAnn,
            system =
              {symIdxBound = NONE,
               varIdxBound = NONE,
               metaIdxBound = NONE,
               hasFreeVars = true,
               hasFreeSyms = false,
               hasFreeMetas = false}}

     | BOUND i =>
         V (var, tau) <:
           {user = userAnn,
            system =
              {symIdxBound = NONE,
               varIdxBound = SOME (i + 1),
               metaIdxBound = NONE,
               hasFreeVars = false,
               hasFreeSyms = false,
               hasFreeMetas = false}}

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

      val operatorAnn = 
        {symIdxBound = symIdxBound,
         varIdxBound = NONE,
         metaIdxBound = NONE,
         hasFreeVars = false,
         hasFreeSyms = hasFreeSyms,
         hasFreeMetas = false}

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
          {symIdxBound = idxBoundForSyms support,
           varIdxBound = NONE,
           metaIdxBound = NONE,
           hasFreeVars = false,
           hasFreeSyms = supportContainsFreeSyms support,
           hasFreeMetas = false}
        end
    
  fun makeMetaTerm (((meta, tau), rs, ms) : meta_term) userAnn =
    let
      val (metaIdxBound, hasFreeMetas) = case meta of FREE _ => (NONE, true) | BOUND j => (SOME (j + 1), false)
      val metaSystemAnn = 
        {symIdxBound = NONE,
         varIdxBound = NONE,
         metaIdxBound = metaIdxBound,
         hasFreeVars = false,
         hasFreeSyms = false,
         hasFreeMetas = hasFreeMetas}
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

    fun abtBindingSupport () : abt binding_support = 
      {abstract = abstractAbt,
       instantiate = raise Match,
       freeVariable = fn (x, tau) => makeVarTerm (FREE x, tau) NONE,
       freeSymbol = P.ret o FREE}

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
             val theta' = O.map (abstractSym (i, j, k) (us, xs, Xs)) theta
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
               val rs' = List.map (fn (r, sigma) => (P.bind (abstractSym (i, j, k) (us, xs, Xs)) r, sigma)) rs
               val ms' = List.map (abstractAbt (i, j, k) (us, xs, Xs)) ms
             in
               makeMetaTerm ((meta, tau), rs', ms') (#user ann)
             end
      end

    and abstractSym (i, j, k) (us, xs, Xs) = 
      fn FREE u =>
         (case indexOfFirst (fn v => Sym.eq (u, v)) us of 
             NONE => P.ret (FREE u)
           | SOME k => P.ret (BOUND (i + k)))
       | BOUND k => P.ret (BOUND k)
  in
    val abtBindingSupport : abt binding_support = abtBindingSupport () 
  end
end