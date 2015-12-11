functor Ast (O : OPERATOR) : AST =
struct
  type symbol = string
  type variable = string
  type metavariable = string

  type 'i operator = 'i O.t
  type 'a spine = 'a O.Arity.Valence.Spine.t

  datatype ast =
      ` of variable
    | $ of symbol operator * btm spine
    | $# of metavariable * (symbol spine * ast spine)
  and btm = \ of (symbol spine * variable spine) * ast
end

functor AstToAbt (X : AST_ABT) : AST_TO_ABT =
struct
  open X

  structure Spine = Abt.Operator.Arity.Valence.Spine

  structure NameEnv =
  struct
    structure Dict = SplayDict (structure Key = StringOrdered)
    open Dict

    type 'a t = 'a dict
    fun fromList xs =
      List.foldl (fn ((n, x), rho) => insert rho n x) empty xs
  end

  fun variable Vs x =
    NameEnv.lookup Vs x
    handle _ =>
      Abt.Variable.named x

  fun symbol Ss u =
    NameEnv.lookup Ss u
    handle _ =>
      Abt.Symbol.named u

  fun convertOpen Th (Ss, Vs) (m, tau) =
    case m of
         Ast.` x => Abt.check Th (Abt.` (variable Vs x), tau)
       | Ast.$ (theta, es) =>
          let
            val (vls, _) = Abt.Operator.arity theta
            val theta' = Abt.Operator.Presheaf.map (symbol Ss) theta
            val es' = Spine.Pair.mapEq (convertOpenBtm Th (Ss, Vs)) (es, vls)
          in
            Abt.check Th (Abt.$ (theta', es'), tau)
          end
       | Ast.$# (mv, (us, ms)) =>
           let
             val ((_, vsorts), _) = Abt.Metacontext.lookup Th mv
             val us' = Spine.Functor.map (symbol Ss) us
             val ms' = Spine.Pair.mapEq (convertOpen Th (Ss, Vs)) (ms, vsorts)
           in
             Abt.check Th (Abt.$# (mv, (us', ms')), tau)
           end
  and convertOpenBtm Th (Ss, Vs) (Ast.\ ((us, xs), m), vl) : Abt.abt Abt.bview =
    let
      val ((ssorts, vsorts), tau) = vl
      val us' = Spine.Functor.map Abt.Symbol.named us
      val xs' = Spine.Functor.map Abt.Variable.named xs
      val Ss' = Spine.Foldable.foldr (fn ((u, u'), Ss') => NameEnv.insert Ss' u u') Ss (Spine.Pair.zipEq (us, us'))
      val Vs' = Spine.Foldable.foldr (fn ((x, x'), Vs') => NameEnv.insert Vs' x x') Vs (Spine.Pair.zipEq (xs, xs'))
    in
      Abt.\ ((us', xs'), convertOpen Th (Ss', Vs') (m, tau))
    end

  fun convert Th m =
    convertOpen Th (NameEnv.empty, NameEnv.empty) m
end
