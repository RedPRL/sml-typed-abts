functor LnScope
  (structure Metavar : ABT_SYMBOL
   structure Var : ABT_SYMBOL
   type sort) : LN_SCOPE =
struct
  type variable = Var.t
  type sort = sort
  type valence = sort list * sort

  datatype ('v, 'a) scope_view = \ of 'v list * 'a
  type 'a scope = (string, 'a) scope_view
  infix \

  exception Instantiate

  type ('m, 'a) binding_support = 
    {abstract: int -> variable list -> 'a -> 'a,
     instantiate: int -> 'm list -> 'a -> 'a,
     freeVariable : variable * sort -> 'm}

  fun liftTraversal f j (xs \ m) = 
    let
      val varCount = List.length xs
    in
      xs \ f (j + varCount) m
    end

  fun eq f (_ \ m, _ \ n) = 
    f (m, n)

  fun intoScope (driver : ('m, 'a) binding_support) (xs \ m) =
    (List.map Var.toString xs) \ #abstract driver 0 xs m

  fun outScope (driver : ('m, 'a) binding_support) taus (xs \ m) =
    let
      val xs' = List.map Var.named xs
      val ms = ListPair.mapEq (#freeVariable driver) (xs', taus)
    in
      xs' \ #instantiate driver 0 ms m
    end

  fun unsafeRead sc = sc
  fun unsafeReadBody (_ \ m) = m
  fun unsafeMakeScope sc = sc
end