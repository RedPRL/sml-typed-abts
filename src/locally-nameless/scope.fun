functor LnScope
  (structure Metavar : ABT_SYMBOL
   structure Var : ABT_SYMBOL
   structure Sym : ABT_SYMBOL
   type sort
   type psort) : LN_SCOPE =
struct
  type metavariable = Metavar.t
  type variable = Var.t
  type symbol = Sym.t
  type sort = sort
  type psort = psort
  type valence = (psort list * sort list) * sort

  datatype ('s, 'v, 'a) scope_view = \ of ('s list * 'v list) * 'a
  type 'a scope = (string, string, 'a) scope_view
  infix \

  exception Instantiate

  type ('m, 'p, 'a) binding_support = 
    {abstract: int * int * int -> symbol list * variable list * metavariable list -> 'a -> 'a,
     instantiate: int * int * int -> 'a -> 'p list * 'm list * 'm scope list -> 'a,
     freeVariable : variable * sort -> 'm,
     freeSymbol : symbol -> 'p}

  fun liftAbstract abstract (i, j, k) (us, xs, Xs) ((us', xs') \ m) =
    let
      val symCount = List.length us
      val varCount = List.length xs
      val metaCount = List.length Xs
    in
      (us', xs') \ abstract (i + symCount, j + varCount, k + metaCount) (us, xs, Xs) m
    end

  fun liftInstantiate instantiate (i, j, k) ((us, xs) \ m) (rs, ms, scs) =
    let
      val symCount = List.length us
      val varCount = List.length xs
    in
      (us, xs) \ instantiate (i + symCount, j + varCount, k) m (rs, ms, scs)
    end

  fun scopeBindingSupport (driver : ('m, 'p, 'a) binding_support) : ('m, 'p, 'a scope) binding_support =
    {abstract = liftAbstract (#abstract driver),
     instantiate = liftInstantiate (#instantiate driver),
     freeVariable = #freeVariable driver,
     freeSymbol = #freeSymbol driver}

  fun eq f (_ \ m, _ \ n) = 
    f (m, n)

  fun intoScope (driver : ('m, 'p, 'a) binding_support) ((us, xs) \ m) =
    (List.map Sym.toString us, List.map Var.toString xs) \ #abstract driver (0,0,0) (us, xs, []) m

  fun outScope (driver : ('m, 'p, 'a) binding_support) ((us, xs) \ m) ((_, taus), tau) =
    let
      val us' = List.map Sym.named us
      val xs' = List.map Var.named xs
      val rs = List.map (#freeSymbol driver) us'
      val ms = ListPair.mapEq (#freeVariable driver) (xs', taus)
    in
      (us', xs') \ #instantiate driver (0,0,0) m (rs, ms, [])
    end

  fun unsafeRead sc = sc
end