(* sorts are the classifiers of various ABTs. They're similar to types but
 * much more coarsly grained. For example in some post-modern ML you might have
 * three sorts
 *  - A sort of types
 *  - A sort of expressions
 *  - A sort of commands
 *
 * A unique feature of this ABT library is the ability to express different sorts
 * and one operator accept arguments of many different sorts.
 *)
signature SORT =
sig
  type t
  structure Eq : EQ where type t = t
  structure Show : SHOW where type t = t
end
