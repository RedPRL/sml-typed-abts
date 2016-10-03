structure ExampleLrVals =
  ExampleLrValsFun(structure Token = LrParser.Token)

structure ExampleLex =
  ExampleLexFun(structure Tokens = ExampleLrVals.Tokens)

structure ExampleParser =
  JoinWithArg
    (structure LrParser = LrParser
     structure ParserData = ExampleLrVals.ParserData
     structure Lex = ExampleLex)

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
  fun stringreader s =
    let
      val pos = ref 0
      val remainder = ref (String.size s)
      fun min(a, b) = if a < b then a else b
    in
      fn n =>
        let
          val m = min(n, !remainder)
          val s = String.substring(s, !pos, m)
          val () = pos := !pos + m
          val () = remainder := !remainder - m
        in
          s
        end
    end

  exception ParseError of Pos.t * string

  fun error fileName (s, pos, pos') : unit =
    raise ParseError (Pos.pos (pos fileName) (pos' fileName), s)

  fun loop () =
    let
      val input = (print "> "; TextIO.inputLine TextIO.stdIn)
    in
      case input of
           NONE => 0
         | SOME str =>
             ((let
                 val lexer = ExampleParser.makeLexer (stringreader (Option.valOf input)) "-"
                 val (result, _) = ExampleParser.parse (1, lexer, error "-", "-")
                 val ast as (Ast.$ (theta, es)) = Ast.out result
                 val (_, tau) = O.arity theta

                 val abt = AstToAbt.convert (Abt.Metavar.Ctx.empty, AstToAbt.NameEnv.empty) (Ast.into ast, tau)
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
