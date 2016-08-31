structure Sort =
struct
  datatype t = EXP | NAT
  val eq : t * t -> bool = op=
  fun toString EXP = "exp"
    | toString NAT = "nat"
end

structure O =
struct
  structure Ar = ListAbtArity (structure S = Sort and PS = AbtEmptySort)
  datatype t = LAM | AP | NUM | LIT of int

  val eq : t * t -> bool = op=
  val toString =
    fn LAM => "lam"
     | AP => "ap"
     | NUM => "num"
     | LIT n => Int.toString n

  local
    open Sort
    fun mkValence p q s = ((p, q), s)
  in
    val arity =
      fn LAM => ([mkValence [] [EXP] EXP], EXP)
       | AP => ([mkValence [] [] EXP, mkValence [] [] EXP], EXP)
       | NUM => ([mkValence [] [] NAT], EXP)
       | LIT _ => ([], NAT)
  end
end

structure Operator = AbtSimpleOperator (O)

structure ParseOperator : PARSE_ABT_OPERATOR =
struct
  structure Operator = Operator

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

  structure TP = TokenParser (LangDef)
  open TP

  val parseInt =
    repeat1 digit wth valOf o Int.fromString o String.implode

  val parseParam = identifier wth Operator.P.VAR


  val parse : O.t CharParser.charParser =
    string "lam" return O.LAM
      || string "ap" return O.AP
      || string "num" return O.NUM
      || parseInt wth O.LIT
end

structure AbtKit =
struct
  structure O = Operator
    and Metavar = AbtSymbol ()
    and Var = AbtSymbol ()
    and Sym = AbtSymbol ()
  type annotation = Pos.t
end

structure Abt = Abt (AbtKit)
structure ShowAbt = DebugShowAbt (Abt)

structure AstKit =
struct
  structure Operator = Operator
  structure Metavar = Abt.Metavar
  type annotation = Pos.t
end

structure Ast = AstUtil (Ast (AstKit))
structure AstToAbt = AstToAbt (structure Abt = Abt and Ast = Ast)

structure ParseAstKit =
struct
  structure Ast = Ast
    and ParseOperator = ParseOperator
    and Metavar = Abt.Metavar
    and CharSet = GreekCharSet
  val setSourcePosition = Ast.annotate
end

structure ParseAst = ParseAst (ParseAstKit)

structure MachineBasis : ABT_MACHINE_BASIS =
struct
  type sign = unit

  structure Cl = AbtClosureUtil (AbtClosure (Abt))
  structure S = AbtMachineState (Cl)

  open Abt Cl O
  infix 0 \
  infix 1 <:
  infix 2 $ `$ $$ $#

  exception InvalidCut

  fun step _ =
    fn LAM `$ _ <: _ => S.VAL
     | AP `$ [_ \ m, _ \ n] <: env => S.CUT ((AP `$ [([],[]) \ S.HOLE, ([],[]) \ S.% n], m) <: env)
     | NUM `$ _ <: _ => S.VAL
     | LIT _ `$ _ <: _ => S.VAL
     | _ => raise Fail "Invalid focus"

  fun cut _ =
    fn (AP `$ [_ \ S.HOLE, _ \ S.% cl], _ \ LAM `$ [(_,[x]) \ mx] <: env) =>
         mx <: Cl.insertVar env x cl
     | _ => raise InvalidCut
end

structure Machine = AbtMachineUtil (AbtMachine (MachineBasis))

structure Example =
struct

  local
    open ParserCombinators CharParser

    infixr 4 << >>
    infixr 3 &&
    infix 2 -- ##
    infix 2 wth suchthat return guard when
    infixr 1 || <|> ??
  in
    (* example of adding custom notation to the generated parser *)

    fun myParser mtable () =
      ParseAst.extend mtable ($ (notation mtable))
    and notation mtable () =
      string "%" >> ($ (myParser mtable)) wth (fn x => Ast.$$ (O.NUM, [Ast.\ (([],[]), x)]))
  end

  fun loop () =
    let
      val input = (print "> "; TextIO.inputLine TextIO.stdIn)
    in
      case input of
           NONE => 0
         | SOME str =>
             ((let
                 val parseResult = CharParser.parseString (myParser Abt.Metavar.named ()) str
                 val ast as (Ast.$ (theta, es)) =
                   case parseResult of
                        Sum.INR ast => Ast.out ast
                      | Sum.INL err => raise Fail err
                 val (_, tau) = O.arity theta

                 val abt = AstToAbt.convert Abt.Metavar.Ctx.empty (Ast.into ast, tau)
                 val abt' = Machine.eval () abt
               in
                 print (ShowAbt.toString abt ^ "  ==>  " ^ ShowAbt.toString abt' ^ "\n\n")
               end
               handle err => print ("Error: " ^ exnMessage err ^ "\n\n"));
              loop ())
    end

  fun main (name, args) =
    (print "\n\nType an expression at the prompt\n\n";
     loop ())
end
