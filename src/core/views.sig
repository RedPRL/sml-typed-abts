signature ABT_VIEWS =
sig
  type 'a spine = 'a list

  (* A [bindf] is a view of a abstraction. This is NOT an abt;
   * a binding is a spine of symbols and variables as well as the
   * underlying 'a (usually an abt) that uses them.
   *)
  datatype ('s, 'v, 'a) bindf =
     \ of ('s spine * 'v spine) * 'a

  (* This is the main interface to be used for interacting with
   * an ABT. When inspected, an standard ABT is just a variable or
   * an operator (the binding case is always wrapped in an operators
   * argument) or a metavariable applied to some collection of
   * symbols and terms
   *)
  datatype ('param, 'psort, 'sym, 'var, 'mvar, 'op, 'a) termf =
      ` of 'var
    | $ of 'op * ('sym, 'var, 'a) bindf spine
    | $# of 'mvar * (('param * 'psort) spine * 'a spine)

  (* The "signature endofunctor". *)
  datatype ('sym, 'var, 'op, 'a) appf =
     `$ of 'op * ('sym, 'var, 'a) bindf spine

  val map
    : ('a -> 'b)
    -> ('param, 'psort, 'sym, 'var, 'mvar, 'op, 'a) termf
    -> ('param, 'psort, 'sym, 'var, 'mvar, 'op, 'b) termf

  val mapBind
    : ('a -> 'b)
    -> ('s, 'v, 'a) bindf
    -> ('s, 'v, 'b) bindf

  val mapApp
    : ('a -> 'b)
    -> ('s, 'v, 'o, 'a) appf
    -> ('s, 'v, 'o, 'b) appf
end
