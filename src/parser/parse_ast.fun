functor ParseAst
  (structure Ast : AST
    where type 'a spine = 'a list
   val setSourcePosition : Pos.t -> Ast.ast -> Ast.ast

   structure CharSet : CHARSET
   structure ParseOperator : PARSE_ABT_OPERATOR
   structure Metavar : ABT_SYMBOL
   sharing type Ast.operator = ParseOperator.Operator.t
   sharing type Ast.param = ParseOperator.Operator.P.term
   sharing type Ast.metavariable = Metavar.t) : PARSE_AST =
struct
  structure Ast = Ast
  structure ParseOperator = ParseOperator

  open ParserCombinators CharParser

  infixr 4 << >>
  infixr 3 &&
  infix 2 -- ##
  infix 2 wth suchthat return guard when
  infixr 1 || <|> ??

  structure LangDef :> LANGUAGE_DEF =
  struct
    type scanner = char CharParser.charParser
    val commentStart = NONE
    val commentEnd = NONE
    val commentLine = NONE
    val nestedComments = true

    val identLetter =
         CharParser.letter
      || CharParser.digit
      || CharSet.char
    val identStart = identLetter
    val opStart = fail "Operators not supported" : scanner
    val opLetter = opStart
    val reservedNames = []
    val reservedOpNames = []
    val caseSensitive = true
  end

  structure TokenParser = TokenParser (LangDef)
  open TokenParser

  type metavariable_table = string -> Ast.metavariable

  fun extend mtable custom : Ast.ast CharParser.charParser =
    let
      val metavariable = symbol "#" >> identifier wth mtable

      fun makeAst (pos, m) = setSourcePosition pos (Ast.into m)

      fun ast () =
        (custom
         || $ app
         || $ metaApp
         || !! identifier wth (fn (x, pos) => makeAst (pos, Ast.` x))) ?? "ast"
      and app () =
        !! ParseOperator.parse
          && opt (parens (semiSep ($ abs)))
          wth (fn ((theta, pos : Pos.t), es) => makeAst (pos, Ast.$ (theta, getOpt (es, []))))
          ?? "operator application"
      and metaApp () =
        !! metavariable
          && opt (braces (commaSep ParseOperator.parseParam))
          && opt (squares (commaSep ($ ast)))
          wth (fn ((x, pos), (ps, ms)) => makeAst (pos, Ast.$# (x, (getOpt (ps, []), getOpt (ms, [])))))
          ?? "metavariable application"
      and properAbs () =
        opt (braces (commaSep identifier))
          && opt (squares (commaSep identifier))
          && dot
          >> $ ast
          wth (fn (us, (xs, m)) => Ast.\ ((getOpt (us, []), getOpt (xs, [])), m))
          ?? "abstractor"
      and pseudoAbs () =
        $ ast wth (fn m => Ast.\ (([], []), m))
      and abs () =
        $ properAbs
          || $ pseudoAbs
    in
      $ ast
    end

    fun parse mtable = extend mtable (parse mtable)
end
