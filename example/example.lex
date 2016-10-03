type pos = string -> Coord.t
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token
type arg = string

val pos = ref Coord.init
val eof = fn (fileName : string) => Tokens.EOF (!pos, !pos)

exception LexerError of pos

%%
%arg (fileName : string);
%header (functor ExampleLexFun (structure Tokens : Example_TOKENS));
alpha = [A-Za-z];
digit = [0-9];
any = [@a-zA-Z0-9\'];
whitespace = [\ \t];
%%

\n                 => (pos := (Coord.nextline o (!pos)); continue ());
{whitespace}+      => (pos := (Coord.addchar (size yytext) o (!pos)); continue ());
{digit}+           => (Tokens.NUMERAL (valOf (Int.fromString yytext), !pos, Coord.addchar (size yytext) o (!pos)));
"//"[^\n]*         => (continue ());

"("                => (Tokens.LPAREN (!pos, Coord.nextchar o (!pos)));
")"                => (Tokens.RPAREN (!pos, Coord.nextchar o (!pos)));
"."                => (Tokens.DOT (!pos, Coord.nextchar o (!pos)));
"#"                => (Tokens.HASH (!pos, Coord.nextchar o (!pos)));
"\\"                => (Tokens.LAMBDA (!pos, Coord.nextchar o (!pos)));

{alpha}{any}*      => (Tokens.IDENT (yytext, !pos, Coord.addchar (size yytext) o (!pos)));

