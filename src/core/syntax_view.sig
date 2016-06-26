signature ABT_SYNTAX_VIEW_INTO =
sig
  type symbol
  type variable
  type metavariable
  type sort
  type 'a operator
  type 'a spine

  type term

  datatype 'a bview =
     \ of (symbol spine * variable spine) * 'a

  datatype 'a view =
     ` of variable
   | $ of symbol operator * 'a bview spine
   | $# of metavariable * ((symbol * sort) spine * 'a spine)

  val check : term view * sort -> term

  val $$ : symbol operator * term bview spine -> term

  val debugToString : term -> string
  val toString : term -> string
end

signature ABT_SYNTAX_VIEW =
sig
  include ABT_SYNTAX_VIEW_INTO

  val infer : term -> term view * sort
  val out : term -> term view
end
