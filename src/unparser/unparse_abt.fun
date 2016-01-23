signature LIST_ABT =
  ABT where type 'a Operator.Arity.Valence.Spine.t = 'a list

functor UnparseAbt
  (structure Abt : LIST_ABT
   structure Unparse : UNPARSE) : UNPARSE_ABT =
struct
  structure Abt = Abt
  structure Unparse = Unparse

  open Abt Unparse
  infix 5 $ $# \

  structure O = Operator and V = Variable and S = Symbol and M = Metavariable
  structure Spine = O.Arity.Valence.Spine

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
             `x => atom @@ V.Show.toString x
           | theta $ es =>
               let
                 val es' = Spine.pretty (parens o done o goB) ";" es
               in
                 atom
                   @@ O.Show.toString S.Show.toString theta
                    ^ (if Spine.isEmpty es then "" else "(" ^ es' ^ ")")
               end
           | v $# (us, ms) =>
               let
                 val us' = Spine.pretty S.Show.toString "," us
                 val ms' = Spine.pretty (parens o done o outer) "," ms
               in
                 atom
                   @@ "#" ^ M.Show.toString v
                    ^ (if Spine.isEmpty us then "" else "{" ^ us' ^ "}")
                    ^ (if Spine.isEmpty ms then "" else "[" ^ ms' ^ "]")
               end
      and goB ((us, xs) \ m) =
        let
          val symEmpty = Spine.isEmpty us
          val varEmpty = Spine.isEmpty xs
          val us' = Spine.pretty S.Show.toString "," us
          val xs' = Spine.pretty V.Show.toString "," xs
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

