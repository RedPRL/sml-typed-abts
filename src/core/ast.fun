functor Ast
  (structure Operator : ABT_OPERATOR
   type annotation) : AST =
struct
  type variable = string
  type metavariable = string
  type annotation = annotation

  type operator = Operator.t

  datatype 'a view =
      ` of variable
    | $ of operator * 'a abs list
    | $# of metavariable * 'a list
  and 'a abs = \ of variable list * 'a

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
     | theta $ [] @: _ => Operator.toString theta
     | theta $ es @: _ => 
         Operator.toString theta
           ^ "(" ^ ListUtil.joinWith toStringB "; " es ^ ")"
     | mv $# es @: _ =>
         let
           val es' = ListUtil.joinWith toString "," es
         in
           "#" ^ mv
               ^ (if ListUtil.isEmpty es then "" else "[" ^ es' ^ "]")
         end

  and toStringB =
    fn (xs \ M) =>
      let
        val varEmpty = ListUtil.isEmpty xs
        val xs' = ListUtil.joinWith (fn x => x) "," xs
      in
         (if varEmpty then "" else "[" ^ xs' ^ "].")
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

  fun variable vnames x =
    NameEnv.lookup vnames x

  exception BadConversion of string * Ast.annotation option

  fun convertOpen (psi, mnames) vnames (m, tau) =
    let
      val oann = Ast.getAnnotation m
      val abt =
        case Ast.out m of
             Ast.` x => Abt.check (Abt.` (variable vnames x), tau)
           | Ast.$ (theta, es) =>
              let
                val (vls, _) = Abt.O.arity theta
                val es' = ListPair.mapEq (convertOpenAbs (psi, mnames) vnames) (es, vls)
                          handle ListPair.UnequalLengths =>
                                 raise BadConversion ("Arity mismatch for operator " ^ Abt.O.toString theta, oann)
              in
                Abt.check (Abt.$ (theta, es'), tau)
              end
           | Ast.$# (mv, ms) =>
               let
                 val mv' = NameEnv.lookup mnames mv
                           handle NameEnv.Absent =>
                                  raise BadConversion ("Free metavariable " ^ mv, oann)
                 val (vsorts, tau') = Abt.Metavar.Ctx.lookup psi mv'
                 val _ = if Abt.O.Ar.Vl.S.eq (tau, tau') then () else raise Fail "Convert: metavariable sort mismatch"
                 val ms' = ListPair.mapEq (convertOpen (psi, mnames) vnames) (ms, vsorts)
               in
                 Abt.check (Abt.$# (mv', ms'), tau)
               end
    in
      case oann of
         SOME ann => Abt.annotate ann abt
       | NONE => abt
    end

  and convertOpenAbs (psi, mnames) vnames (Ast.\ (xs, m), vl) : Abt.abt Abt.bview =
    let
      val (vsorts, tau) = vl
      val xs' = List.map Abt.Var.named xs
      val vnames' = List.foldr (fn ((x, x'), vnames') => NameEnv.insert vnames' x x') vnames (ListPair.zipEq (xs, xs'))
    in
      Abt.\ (xs', convertOpen (psi, mnames) vnames' (m, tau))
    end

  fun convert (psi, mnames) =
    convertOpen (psi, mnames) NameEnv.empty
end
