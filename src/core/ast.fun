functor Ast
  (structure Operator : ABT_OPERATOR
   type annotation) : AST =
struct
  type symbol = string
  type variable = string
  type metavariable = string
  type annotation = annotation

  structure P = Operator.P

  type 'i operator = 'i Operator.t
  type 'i param = 'i Operator.P.term
  type 'a spine = 'a list

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
     | theta $ [] @: _ => Operator.toString (fn x => x) theta
     | theta $ es @: _ => 
         Operator.toString (fn x => x) theta
           ^ "(" ^ ListSpine.pretty toStringB "; " es ^ ")"
     | mv $# (us, es) @: _ =>
         let
           val us' = ListSpine.pretty (P.toString (fn x => x)) "," us
           val es' = ListSpine.pretty toString "," es
         in
           "#" ^ mv
               ^ (if ListSpine.isEmpty us then "" else "{" ^ us' ^ "}")
               ^ (if ListSpine.isEmpty es then "" else "[" ^ es' ^ "]")
         end

  and toStringB =
    fn ((us, xs) \ M) =>
      let
        val symEmpty = ListSpine.isEmpty us
        val varEmpty = ListSpine.isEmpty xs
        val us' = ListSpine.pretty (fn x => x) "," us
        val xs' = ListSpine.pretty (fn x => x) "," xs
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

  structure NameEnv = SplayDict (structure Key = StringOrdered)
  structure PF = MonadApplicative (Abt.O.P)

  fun variable vnames x =
    NameEnv.lookup vnames x
    handle _ =>
      Abt.Var.named x

  fun symbol snames u =
    NameEnv.lookup snames u
    handle _ =>
      Abt.Sym.named u

  exception BadConversion of string * Ast.annotation option

  fun convertOpen (psi, mnames) (snames, vnames) (m, tau) =
    let
      val oann = Ast.getAnnotation m
      val abt =
        case Ast.out m of
             Ast.` x => Abt.check (Abt.` (variable vnames x), tau)
           | Ast.$ (theta, es) =>
              let
                val (vls, _) = Abt.O.arity theta
                val theta' = Abt.O.map (PF.pure o symbol snames) theta
                val es' = ListPair.mapEq (convertOpenAbs (psi, mnames) (snames, vnames)) (es, vls)
                          handle ListPair.UnequalLengths =>
                                 raise BadConversion ("Arity mismatch for operator " ^ Abt.O.toString (fn x => x) theta, oann)
              in
                Abt.check (Abt.$ (theta', es'), tau)
              end
           | Ast.$# (mv, (ps, ms)) =>
               let
                 val mv' = NameEnv.lookup mnames mv
                           handle NameEnv.Absent =>
                                  raise BadConversion ("Free metavariable " ^ mv, oann)
                 val ((ssorts, vsorts), tau') = Abt.Metavar.Ctx.lookup psi mv'
                 val _ = if Abt.O.Ar.Vl.S.eq (tau, tau') then () else raise Fail "Convert: metavariable sort mismatch"
                 val ps' = ListPair.zipEq (List.map (PF.map (symbol snames)) ps, ssorts)
                 val ms' = ListPair.mapEq (convertOpen (psi, mnames) (snames, vnames)) (ms, vsorts)
               in
                 Abt.check (Abt.$# (mv', (ps', ms')), tau)
               end
    in
      case oann of
         SOME ann => Abt.annotate ann abt
       | NONE => abt
    end

  and convertOpenAbs (psi, mnames) (snames, vnames) (Ast.\ ((us, xs), m), vl) : Abt.abt Abt.bview =
    let
      val ((ssorts, vsorts), tau) = vl
      val us' = List.map Abt.Sym.named us
      val xs' = List.map Abt.Var.named xs
      val snames' = List.foldr (fn ((u, u'), snames') => NameEnv.insert snames' u u') snames (ListPair.zipEq (us, us'))
      val vnames' = List.foldr (fn ((x, x'), vnames') => NameEnv.insert vnames' x x') vnames (ListPair.zipEq (xs, xs'))
    in
      Abt.\ ((us', xs'), convertOpen (psi, mnames) (snames', vnames') (m, tau))
    end

  fun convert (psi, mnames) =
    convertOpen (psi, mnames) (NameEnv.empty, NameEnv.empty)
end
