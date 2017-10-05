signature ABT_VIEWS =
sig
  type 'a spine = 'a list

  (* A [bindf] is a view of a abstraction. This is NOT an abt;
   * a binding is a spine of symbols and variables as well as the
   * underlying 'a (usually an abt) that uses them.
   *)
  datatype ('v, 'a) bindf =
     \ of 'v spine * 'a

  (* This is the main interface to be used for interacting with
   * an ABT. When inspected, an standard ABT is just a variable or
   * an operator (the binding case is always wrapped in an operators
   * argument) or a metavariable applied to some collection of
   * symbols and terms
   *)
  datatype ('var, 'mvar, 'op, 'a) termf =
      ` of 'var
    | $ of 'op * ('var, 'a) bindf spine
    | $# of 'mvar * 'a spine

  (* The "signature endofunctor". *)
  datatype ('var, 'op, 'a) appf =
     `$ of 'op * ('var, 'a) bindf spine

  val map
    : ('a -> 'b)
    -> ('var, 'mvar, 'op, 'a) termf
    -> ('var, 'mvar, 'op, 'b) termf

  val mapBind
    : ('a -> 'b)
    -> ('v, 'a) bindf
    -> ('v, 'b) bindf

  val mapApp
    : ('a -> 'b)
    -> ('v, 'o, 'a) appf
    -> ('v, 'o, 'b) appf
end
