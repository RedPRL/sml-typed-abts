functor Ast
  (structure Operator : ABT_OPERATOR
   structure Metavar : ABT_SYMBOL
   type annotation) : AST =
struct
  type symbol = string
  type variable = string
  type metavariable = Metavar.t
  type annotation = annotation

  structure Sp = Operator.Ar.Vl.Sp
  structure P = Operator.P

  type 'i operator = 'i Operator.t
  type 'i param = 'i Operator.P.term
  type 'a spine = 'a Sp.t

  datatype 'a view =
      ` of variable
    | $ of symbol operator * 'a abs spine
    | $# of metavariable * (symbol param spine * 'a spine)
  and 'a abs = \ of (symbol spine * variable spine) * 'a

  datatype ast = @: of ast view * annotation option

  infix $ $# \
  infix @:

  fun into m = m @: NONE
  fun out (m @: _) = m

  fun getAnnotation (m @: ann) = ann
  fun setAnnotation ann (m @: _) = m @: ann
  fun annotate ann (m @: _) = m @: SOME ann
  fun clearAnnotation (m @: _) = m @: NONE

  val rec toString =
    fn `x @: _ => x
     | theta $ es @: _ =>
         if Sp.isEmpty es then
           Operator.toString (fn x => x) theta
         else
           Operator.toString (fn x => x) theta
              ^ "(" ^ Sp.pretty toStringB "; " es ^ ")"
     | mv $# (us, es) @: _ =>
         let
           val us' = Sp.pretty (P.toString (fn x => x)) "," us
           val es' = Sp.pretty toString "," es
         in
           "#" ^ Metavar.toString mv
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

functor AstUtil (Ast : AST) : AST_UTIL =
struct
  open Ast

  val `` = into o `
  val $$ = into o $
  val $$# = into o $#
end

functor AstToAbt (X : AST_ABT) : AST_TO_ABT =
struct
  open X

  structure Sp = Abt.O.Ar.Vl.Sp

  structure NameEnv = SplayDict (structure Key = StringOrdered)

  structure PF = FunctorOfMonad (Abt.O.P)

  fun variable vnames x =
    NameEnv.lookup vnames x
    handle _ =>
      Abt.Var.named x

  fun symbol snames u =
    NameEnv.lookup snames u
    handle _ =>
      Abt.Sym.named u

  fun convertOpen psi (snames, vnames) (m, tau) =
    let
      val abt =
        case Ast.out m of
             Ast.` x => Abt.check (Abt.` (variable vnames x), tau)
           | Ast.$ (theta, es) =>
              let
                val (vls, _) = Abt.O.arity theta
                val theta' = Abt.O.map (Abt.O.P.pure o symbol snames) theta
                val es' = Sp.Pair.mapEq (convertOpenAbs psi (snames, vnames)) (es, vls)
              in
                Abt.check (Abt.$ (theta', es'), tau)
              end
           | Ast.$# (mv, (ps, ms)) =>
               let
                 val ((ssorts, vsorts), _) = Abt.Metavar.Ctx.lookup psi mv
                 val ps' = Sp.Pair.zipEq (Sp.map (PF.map (symbol snames)) ps, ssorts)
                 val ms' = Sp.Pair.mapEq (convertOpen psi (snames, vnames)) (ms, vsorts)
               in
                 Abt.check (Abt.$# (mv, (ps', ms')), tau)
               end
    in
      case Ast.getAnnotation m of
         SOME ann => Abt.annotate ann abt
       | NONE => abt
    end

  and convertOpenAbs psi (snames, vnames) (Ast.\ ((us, xs), m), vl) : Abt.abt Abt.bview =
    let
      val ((ssorts, vsorts), tau) = vl
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
