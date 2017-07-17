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
     hasFreeVars: bool,
     hasFreeSyms: bool}
  
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
     hasFreeVars = #hasFreeVars ann1 orelse #hasFreeVars ann2,
     hasFreeSyms = #hasFreeSyms ann1 orelse #hasFreeSyms ann2}

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
      val {symIdxBound, varIdxBound, hasFreeVars, hasFreeSyms} = #system ann
      val symIdxBound' = Option.map (fn i => i - List.length us) symIdxBound 
      val varIdxBound' = Option.map (fn i => i - List.length xs) varIdxBound
    in
      {user = #user ann,
       system =
         {symIdxBound = symIdxBound',
          varIdxBound = varIdxBound',
          hasFreeSyms = hasFreeSyms,
          hasFreeVars = hasFreeVars}}
    end

  fun makeVarTerm (var, tau) userAnn = 
    case var of 
       FREE x =>
         V (var, tau) <:
           {user = userAnn,
            system =
              {symIdxBound = NONE,
               varIdxBound = NONE,
               hasFreeVars = true,
               hasFreeSyms = false}}

     | BOUND i =>
         V (var, tau) <:
           {user = userAnn,
            system =
              {symIdxBound = NONE,
               varIdxBound = SOME (i + 1),
               hasFreeVars = false,
               hasFreeSyms = false}}

  fun makeAppTerm (theta, scopes) userAnn =
    let
      val support = O.support theta
      val hasFreeSyms = case support of [] => false | _ => true
      val symIdxBound =
        List.foldr
          (fn ((FREE _,_), oidx) => oidx
            | ((BOUND i, _), NONE) => SOME i
            | ((BOUND i, _), SOME j) => SOME (Int.max (i, j)))
          NONE
          support

      val operatorAnn = 
        {symIdxBound = symIdxBound,
         varIdxBound = NONE,
         hasFreeVars = false,
         hasFreeSyms = hasFreeSyms}

      val systemAnn =
        List.foldr
          (fn (scope, ann) => systemAnnLub (ann, #system (scopeReadAnn scope)))
          operatorAnn
          scopes
    in
      APP (theta, scopes) <: {user = userAnn, system = systemAnn}
    end

  local
    fun indexOfFirst pred xs = 
      let
        fun aux (i, []) = NONE
          | aux (i, x::xs) = if pred x then SOME i else aux (i + 1, xs)
      in
        aux (0, xs)
      end

    fun abstractVarTerm (i, j, k) (us, xs, Xs) = 
      fn (FREE x, tau) => 
         (case indexOfFirst (fn y => Var.eq (x, y)) xs of
             NONE => (FREE x, tau)
           | SOME j' => (BOUND (j + j'), tau))
       | (BOUND l, tau) => (BOUND l, tau)

    fun abtBindingSupport () : abt binding_support = 
      {abstract = abstractAbt,
       instantiate = raise Match,
       freeVariable = fn (x, tau) => makeVarTerm (FREE x, tau) NONE,
       freeSymbol = P.ret o FREE}

    and abstractAbt (i, j, k) (us, xs, Xs) (term <: ann) =
      let
        val {hasFreeSyms, hasFreeVars, ...} = #system ann
      in
        if not (hasFreeSyms orelse hasFreeVars) then term <: ann else 
        case term of
           V varTerm =>
             if not hasFreeVars then term <: ann else
               makeVarTerm (abstractVarTerm (i, j, k) (us, xs, Xs) varTerm) (#user ann)
         | APP (theta, scopes) =>
           let
             val psi = 
               fn FREE u =>
                  (case indexOfFirst (fn v => Sym.eq (u, v)) us of 
                      NONE => P.ret (FREE u)
                    | SOME k => P.ret (BOUND (i + k)))
                | BOUND k => P.ret (BOUND k)
             val scopeBindingSupport = Sc.scopeBindingSupport (abtBindingSupport ())
             val theta' = O.map psi theta
             val scopes' = List.map (#abstract scopeBindingSupport (i, j, k) (us, xs, Xs)) scopes
           in
             makeAppTerm (theta', scopes') (#user ann)
           end
         | META ((X, tau), ps, ms) => raise Match
      end
  in
    val abtBindingSupport : abt binding_support = abtBindingSupport () 
  end
end