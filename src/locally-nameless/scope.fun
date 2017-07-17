functor LnScope
  (structure Var : ABT_SYMBOL
   structure Sym : ABT_SYMBOL
   type sort
   type psort) : LN_SCOPE =
struct
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
    {abstract: int * int -> symbol list * variable list -> 'a -> 'a,
     instantiate: int * int -> 'a -> 'p list * 'm list -> 'a,
     freeVariable : variable * sort -> 'm,
     freeSymbol : symbol -> 'p}

  fun liftAbstract abstract (i, j) (us, xs) ((us', xs') \ m) =
    let
      val symValence = List.length us
      val varValence = List.length xs
    in
      (us', xs') \ abstract (i + symValence, j + varValence) (us, xs) m
    end

  fun liftInstantiate instantiate (i, j) ((us, xs) \ m) (rs, ms) =
    let
      val symValence = List.length us
      val varValence = List.length xs
    in
      (us, xs) \ instantiate (i + symValence, j + varValence) m (rs, ms)
    end

  fun scopeBindingSupport (driver : ('m, 'p, 'a) binding_support) : ('m, 'p, 'a scope) binding_support =
    {abstract = liftAbstract (#abstract driver),
     instantiate = liftInstantiate (#instantiate driver),
     freeVariable = #freeVariable driver,
     freeSymbol = #freeSymbol driver}

  fun eq f (_ \ m, _ \ n) = 
    f (m, n)

  fun intoScope (driver : ('m, 'p, 'a) binding_support) ((us, xs) \ m) =
    (List.map Sym.toString us, List.map Var.toString xs) \ #abstract driver (0,0) (us, xs) m

  fun outScope (driver : ('m, 'p, 'a) binding_support) ((us, xs) \ m) ((_, taus), tau) =
    let
      val us' = List.map Sym.named us
      val xs' = List.map Var.named xs
      val rs = List.map (#freeSymbol driver) us'
      val ms = ListPair.mapEq (#freeVariable driver) (xs', taus)
    in
      (us', xs') \ #instantiate driver (0,0) m (rs, ms)
    end

  fun unsafeRead sc = sc
end