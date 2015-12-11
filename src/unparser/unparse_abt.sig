signature UNPARSE_ABT =
sig
  structure Abt : ABT
  structure Unparse : UNPARSE

  val unparse
    : (Abt.abt -> string Unparse.part option) (* custom notation *)
    -> Abt.abt
    -> string Unparse.part
end
