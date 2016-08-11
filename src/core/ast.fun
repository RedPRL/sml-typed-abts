functor Ast
  (structure Operator : ABT_OPERATOR
   structure Metavar : ABT_SYMBOL
   structure P : ABT_PARAM) : AST =
struct
  type symbol = string
  type variable = string
  type metavariable = Metavar.t
  type param = symbol P.t

  structure P = P and Sp = Operator.Ar.Vl.Sp

  type 'i operator = 'i Operator.t
  type 'a spine = 'a Sp.t

  datatype ast =
      ` of variable
    | $ of param operator * abs spine
    | $# of metavariable * (param spine * ast spine)
  and abs = \ of (symbol spine * variable spine) * ast

  infix $ $# \

  val rec toString =
    fn `x => x
     | theta $ es =>
         if Sp.isEmpty es then
           Operator.toString (P.toString (fn x => x)) theta
         else
           Operator.toString (P.toString (fn x => x)) theta
              ^ "(" ^ Sp.pretty toStringB "; " es ^ ")"
     | mv $# (ps, es) =>
         let
           val ps' = Sp.pretty (P.toString (fn x => x)) "," ps
           val es' = Sp.pretty toString "," es
         in
           "#" ^ Metavar.toString mv
               ^ (if Sp.isEmpty ps then "" else "{" ^ ps' ^ "}")
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

  structure Sp = Abt.O.Ar.Vl.Sp
  structure NameEnv = SplayDict (structure Key = StringOrdered)
  structure P =
  struct
    open Abt.P
    local structure Functor = FunctorOfMonad (Abt.P) in open Functor end
  end

  fun variable vnames x =
    NameEnv.lookup vnames x
    handle _ =>
      Abt.Var.named x

  fun symbol snames u =
    NameEnv.lookup snames u
    handle _ =>
      Abt.Sym.named u

  fun convertOpen psi (snames, vnames) (m, tau) =
    case m of
         Ast.` x => Abt.check (Abt.` (variable vnames x), tau)
       | Ast.$ (theta, es) =>
          let
            val (vls, _) = Abt.O.arity theta
            val theta' = Abt.O.map (P.map (symbol snames)) theta
            val es' = Sp.Pair.mapEq (convertOpenAbs psi (snames, vnames)) (es, vls)
          in
            Abt.check (Abt.$ (theta', es'), tau)
          end
       | Ast.$# (mv, (ps, ms)) =>
           let
             val ((psorts, vsorts), _) = Abt.Metavar.Ctx.lookup psi mv
             val ps' = Sp.Pair.zipEq (Sp.map (P.map (symbol snames)) ps, psorts)
             val ms' = Sp.Pair.mapEq (convertOpen psi (snames, vnames)) (ms, vsorts)
           in
             Abt.check (Abt.$# (mv, (ps', ms')), tau)
           end

  and convertOpenAbs psi (snames, vnames) (Ast.\ ((us, xs), m), vl) : Abt.abt Abt.bview =
    let
      val ((psorts, vsorts), tau) = vl
      val us' = Sp.map Abt.Sym.named us
      val xs' = Sp.map Abt.Var.named xs
      val snames' = Sp.foldr (fn ((u, u'), snames') => NameEnv.insert snames' u u') snames (Sp.Pair.zipEq (us, us'))
      val vnames' = Sp.foldr (fn ((x, x'), vnames') => NameEnv.insert vnames' x x') vnames (Sp.Pair.zipEq (xs, xs'))
    in
      Abt.\ ((us', xs'), convertOpen psi (snames', vnames') (m, tau))
    end

  fun convert psi m =
    convertOpen psi (NameEnv.empty, NameEnv.empty) m
end
