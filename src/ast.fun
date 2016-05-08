functor Ast
  (structure Operator : OPERATOR
   structure Metavariable : PRESYMBOL) : AST =
struct
  type symbol = string
  type variable = string
  type metavariable = Metavariable.t

  structure Spine = Operator.Arity.Valence.Spine

  type 'i operator = 'i Operator.t
  type 'a spine = 'a Spine.t

  datatype ast =
      ` of variable
    | $ of symbol operator * abs spine
    | $# of metavariable * (symbol spine * ast spine)
  and abs = \ of (symbol spine * variable spine) * ast

  infix $ $# \

  val rec toString =
    fn `x => x
     | theta $ es =>
         if Spine.isEmpty es then
           Operator.toString (fn x => x) theta
         else
           Operator.toString (fn x => x) theta
              ^ "(" ^ Spine.pretty toStringB "; " es ^ ")"
     | mv $# (us, es) =>
         let
           val us' = Spine.pretty (fn x => x) "," us
           val es' = Spine.pretty toString "," es
         in
           "#" ^ Metavariable.toString mv
               ^ (if Spine.isEmpty us then "" else "{" ^ us' ^ "}")
               ^ (if Spine.isEmpty es then "" else "[" ^ es' ^ "]")
         end

  and toStringB =
    fn ((us, xs) \ M) =>
      let
        val symEmpty = Spine.isEmpty us
        val varEmpty = Spine.isEmpty xs
        val us' = Spine.pretty (fn x => x) "," us
        val xs' = Spine.pretty (fn x => x) "," xs
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

  structure Spine = Abt.Operator.Arity.Valence.Spine

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
            val es' = Spine.Pair.mapEq (convertOpenAbs psi (snames, vnames)) (es, vls)
          in
            Abt.check (Abt.$ (theta', es'), tau)
          end
       | Ast.$# (mv, (us, ms)) =>
           let
             val ((ssorts, vsorts), _) = Abt.MetaCtx.lookup psi mv
             val us' = Spine.Pair.zipEq (Spine.map (symbol snames) us, ssorts)
             val ms' = Spine.Pair.mapEq (convertOpen psi (snames, vnames)) (ms, vsorts)
           in
             Abt.check (Abt.$# (mv, (us', ms')), tau)
           end

  and convertOpenAbs psi (snames, vnames) (Ast.\ ((us, xs), m), vl) : Abt.abt Abt.bview =
    let
      val ((ssorts, vsorts), tau) = vl
      val us' = Spine.map Abt.Symbol.named us
      val xs' = Spine.map Abt.Variable.named xs
      val snames' = Spine.foldr (fn ((u, u'), snames') => NameEnv.insert snames' u u') snames (Spine.Pair.zipEq (us, us'))
      val vnames' = Spine.foldr (fn ((x, x'), vnames') => NameEnv.insert vnames' x x') vnames (Spine.Pair.zipEq (xs, xs'))
    in
      Abt.\ ((us', xs'), convertOpen psi (snames', vnames') (m, tau))
    end

  fun convert psi m =
    convertOpen psi (NameEnv.empty, NameEnv.empty) m
end
