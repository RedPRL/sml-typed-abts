functor ParseAst
  (structure Ast : AST
    where type 'a spine = 'a list
   structure ParseOperator : PARSE_OPERATOR
   structure Metavariable : PRESYMBOL
   sharing type Ast.operator = ParseOperator.Operator.t
   sharing type Ast.metavariable = Metavariable.t) : PARSE_AST =
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
        || digit
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

  fun parse mtable : Ast.ast CharParser.charParser =
    let
      val variable = identifier
      val parameter = identifier
      val metavariable = symbol "#" >> identifier wth mtable

      fun ast () =
        ($ app
         || $ metaApp
         || variable wth Ast.`) ?? "ast"
      and app () =
        ParseOperator.parse
          && opt (parens (semiSep ($ abs)))
          wth (fn (theta, es) => Ast.$ (theta, getOpt (es, [])))
          ?? "operator application"
      and metaApp () =
        metavariable
          && opt (braces (commaSep parameter))
          && opt (squares (commaSep ($ ast)))
          wth (fn (x, (us, ms)) => Ast.$# (x, (getOpt (us, []), getOpt (ms, []))))
          ?? "metavariable application"
      and properAbs () =
        opt (braces (commaSep parameter))
          && opt (squares (commaSep variable))
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
end
