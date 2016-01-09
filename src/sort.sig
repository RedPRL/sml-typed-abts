(* sorts are the classifiers of ABTs. They can be thought of as the various syntactic
 * categories one encounters when describing a grammar. They're similar to types but
 * much more coarsly grained. For example in some post-modern ML you might have
 * three sorts
 *  - A sort of types
 *  - A sort of expressions
 *  - A sort of commands
 *
 * A unique feature of this ABT library is the ability to express different sorts.
 * Specifically, you can define operators which take arguments of different sorts so
 * that it's not necessary to lump types + expressions + whatever else into the same
 * collection of objects with anything distinguishing them.
 *)
signature SORT =
sig
  type t
  structure Eq : EQ where type t = t
  structure Show : SHOW where type t = t
end
