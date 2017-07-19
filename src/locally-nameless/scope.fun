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
     instantiate: int * int * int -> 'p list * 'm list * 'm scope list -> 'a -> 'a,
     freeVariable : variable * sort -> 'm,
     freeSymbol : symbol -> 'p}

  fun liftTraversal f (i, j, k) ((us, xs) \ m) = 
    let
      val symCount = List.length us
      val varCount = List.length xs
    in
      (us, xs) \ f (i + symCount, j + varCount, k) m
    end

  fun eq f (_ \ m, _ \ n) = 
    f (m, n)

  fun intoScope (driver : ('m, 'p, 'a) binding_support) ((us, xs) \ m) =
    (List.map Sym.toString us, List.map Var.toString xs) \ #abstract driver (0,0,0) (us, xs, []) m

  fun outScope (driver : ('m, 'p, 'a) binding_support) (_, taus) ((us, xs) \ m) =
    let
      val us' = List.map Sym.named us
      val xs' = List.map Var.named xs
      val rs = List.map (#freeSymbol driver) us'
      val ms = ListPair.mapEq (#freeVariable driver) (xs', taus)
    in
      (us', xs') \ #instantiate driver (0,0,0) (rs, ms, []) m
    end

  fun unsafeRead sc = sc
  fun unsafeReadBody (_ \ m) = m
end