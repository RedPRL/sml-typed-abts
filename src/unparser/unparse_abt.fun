signature LIST_ABT =
  ABT where type 'a O.Ar.Vl.Sp.t = 'a list

functor UnparseAbt
  (structure Abt : LIST_ABT
   structure Unparse : UNPARSE) : UNPARSE_ABT =
struct
  structure Abt = Abt
  structure Unparse = Unparse

  open Abt Unparse
  infix 5 $ $# \

  structure V = Var and S = Sym and M = Metavar and P = Abt.O.P
  structure Sp = O.Ar.Vl.Sp

  type unparser = Abt.abt -> string Unparse.part

  fun @@ (f, x) = f x
  infix 0 @@

  fun unparse inner =
    let
      fun outer m =
        case inner m of
             SOME p => p
           | NONE => go m
      and go m =
        case Abt.out m of
             `x => atom @@ V.toString x
           | theta $ es =>
               let
                 val es' = Sp.pretty (parens o done o goB) ";" es
               in
                 atom
                   @@ O.toString S.toString theta
                    ^ (if Sp.isEmpty es then "" else "(" ^ es' ^ ")")
               end
           | x $# (ps, ms) =>
               let
                 val ps' = Sp.pretty (P.toString S.toString o #1) "," ps
                 val ms' = Sp.pretty (parens o done o outer) "," ms
               in
                 atom
                   @@ "#" ^ M.toString x
                    ^ (if Sp.isEmpty ps then "" else "{" ^ ps' ^ "}")
                    ^ (if Sp.isEmpty ms then "" else "[" ^ ms' ^ "]")
               end
      and goB ((us, xs) \ m) =
        let
          val symEmpty = Sp.isEmpty us
          val varEmpty = Sp.isEmpty xs
          val us' = Sp.pretty S.toString "," us
          val xs' = Sp.pretty V.toString "," xs
        in
          atom
            @@ (if symEmpty then "" else "{" ^ us' ^ "}")
             ^ (if varEmpty then "" else "[" ^ xs' ^ "]")
             ^ (if symEmpty andalso varEmpty then "" else ".")
             ^ parens (done (outer m))
        end
    in
      outer
    end
end
