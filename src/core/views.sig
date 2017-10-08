signature ABT_VIEWS =
sig
  (* A [bindf] is a view of a abstraction. This is NOT an abt;
   * a binding is a list of variables as well as the
   * underlying 'a (usually an abt) that uses them.
   *)
  datatype ('v, 'a) bindf =
     \ of 'v list * 'a

  (* This is the main interface to be used for interacting with
   * an ABT. When inspected, an standard ABT is just a variable or
   * an operator (the binding case is always wrapped in an operators
   * argument) or a metavariable applied to some list of terms
   *)
  datatype ('var, 'mvar, 'op, 'a) termf =
      ` of 'var
    | $ of 'op * ('var, 'a) bindf list
    | $# of 'mvar * 'a list

  (* The "signature endofunctor". *)
  datatype ('var, 'op, 'a) appf =
     `$ of 'op * ('var, 'a) bindf list

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
