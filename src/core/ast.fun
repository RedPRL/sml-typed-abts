functor Ast
  (structure Operator : ABT_OPERATOR
   structure Metavariable : ABT_SYMBOL) : AST =
struct
  type symbol = string
  type variable = string
  type metavariable = Metavariable.t

  structure Sp = Operator.Ar.Vl.Sp

  type 'i operator = 'i Operator.t
  type 'a spine = 'a Sp.t

  datatype ast =
      ` of variable
    | $ of symbol operator * abs spine
    | $# of metavariable * (symbol spine * ast spine)
  and abs = \ of (symbol spine * variable spine) * ast

  infix $ $# \

  val rec toString =
    fn `x => x
     | theta $ es =>
         if Sp.isEmpty es then
           Operator.toString (fn x => x) theta
         else
           Operator.toString (fn x => x) theta
              ^ "(" ^ Sp.pretty toStringB "; " es ^ ")"
     | mv $# (us, es) =>
         let
           val us' = Sp.pretty (fn x => x) "," us
           val es' = Sp.pretty toString "," es
         in
           "#" ^ Metavariable.toString mv
               ^ (if Sp.isEmpty us then "" else "{" ^ us' ^ "}")
               ^ (if Sp.isEmpty es then "" else "[" ^ es' ^ "]")
         end

  and toStringB =
    fn ((us, xs) \ M) =>
      let
        val symEmpty = Sp.isEmpty us
        val varEmpty = Sp.isEmpty xs
        val us' = Sp.pretty (fn x => x) "," us
        val xs' = Sp.pretty (fn x => x) "," xs
      in
        (if symEmpty then "" else "{" ^ us' ^ "}")
          ^ (if varEmpty then "" else "[" ^ xs' ^ "]")
          ^ (if symEmpty andalso varEmpty then "" else ".")
          ^ toString M
      end
end

functor AstToAbt (X : AST_ABT) : AST_TO_ABT =
struct
  open X

  structure Sp = Abt.Operator.Ar.Vl.Sp

  structure NameEnv = SplayDict (structure Key = StringOrdered)

  fun variable vnames x =
    NameEnv.lookup vnames x
    handle _ =>
      Abt.Variable.named x

  fun symbol snames u =
    NameEnv.lookup snames u
    handle _ =>
      Abt.Symbol.named u

  fun convertOpen psi (snames, vnames) (m, tau) =
    case m of
         Ast.` x => Abt.check (Abt.` (variable vnames x), tau)
       | Ast.$ (theta, es) =>
          let
            val (vls, _) = Abt.Operator.arity theta
            val theta' = Abt.Operator.map (symbol snames) theta
            val es' = Sp.Pair.mapEq (convertOpenAbs psi (snames, vnames)) (es, vls)
          in
            Abt.check (Abt.$ (theta', es'), tau)
          end
       | Ast.$# (mv, (us, ms)) =>
           let
             val ((ssorts, vsorts), _) = Abt.Metavariable.Ctx.lookup psi mv
             val us' = Sp.Pair.zipEq (Sp.map (symbol snames) us, ssorts)
             val ms' = Sp.Pair.mapEq (convertOpen psi (snames, vnames)) (ms, vsorts)
           in
             Abt.check (Abt.$# (mv, (us', ms')), tau)
           end

  and convertOpenAbs psi (snames, vnames) (Ast.\ ((us, xs), m), vl) : Abt.abt Abt.bview =
    let
      val ((ssorts, vsorts), tau) = vl
      val us' = Sp.map Abt.Symbol.named us
      val xs' = Sp.map Abt.Variable.named xs
      val snames' = Sp.foldr (fn ((u, u'), snames') => NameEnv.insert snames' u u') snames (Sp.Pair.zipEq (us, us'))
      val vnames' = Sp.foldr (fn ((x, x'), vnames') => NameEnv.insert vnames' x x') vnames (Sp.Pair.zipEq (xs, xs'))
    in
      Abt.\ ((us', xs'), convertOpen psi (snames', vnames') (m, tau))
    end

  fun convert psi m =
    convertOpen psi (NameEnv.empty, NameEnv.empty) m
end
