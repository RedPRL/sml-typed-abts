signature LN_SCOPE =
sig
  type 'a scope

  type variable
  type sort

  exception Instantiate

  val liftTraversal : (int -> 'a -> 'b) -> int -> 'a scope -> 'b scope

  (* TODO: delete? *)
  type ('m, 'a) binding_support = 
    {abstract: int -> variable list -> 'a -> 'a,
     instantiate: int -> 'm list -> 'a -> 'a,
     freeVariable : variable * sort -> 'm}

  datatype ('v, 'a) scope_view = \ of 'v list * 'a

  val eq : ('a * 'a -> bool) -> 'a scope * 'a scope -> bool

  val intoScope : ('m, 'a) binding_support -> (variable, 'a) scope_view -> 'a scope 
  val outScope : ('m, 'a) binding_support -> sort list -> 'a scope -> (variable, 'a) scope_view

  (* O(1) *)
  val unsafeRead : 'a scope -> (string, 'a) scope_view
  val unsafeReadBody : 'a scope -> 'a
  val unsafeMakeScope : (string, 'a) scope_view -> 'a scope
end