signature AST =
sig
  type 'i operator
  type 'i param
  type 'a spine

  type symbol = string
  type variable = string
  type metavariable = string

  type annotation
  type ast

  datatype 'a view =
      ` of variable
    | $ of symbol operator * 'a abs spine
    | $# of metavariable * (symbol param spine * 'a spine)
  and 'a abs = \ of (symbol spine * variable spine) * 'a

  val into : ast view -> ast
  val out : ast -> ast view

  val annotate : annotation -> ast -> ast
  val getAnnotation : ast -> annotation option
  val setAnnotation : annotation option -> ast -> ast
  val clearAnnotation : ast -> ast

  val toString : ast -> string
end

signature AST_UTIL =
sig
  include AST

  val `` : variable -> ast
  val $$ : symbol operator * ast abs spine -> ast
  val $$# : metavariable * (symbol param spine * ast spine) -> ast
end

signature AST_ABT =
sig
  structure Abt : ABT
  structure Ast : AST

  sharing type Ast.operator = Abt.O.t
  sharing type Ast.spine = Abt.O.Ar.Vl.Sp.t
  sharing type Ast.annotation = Abt.annotation
  sharing type Ast.param = Abt.O.P.term
end

signature AST_TO_ABT =
sig
  include AST_ABT

  structure NameEnv : DICT where type key = string

  exception BadConversion of string * Ast.annotation option

  (* convert a closed ast to an abt *)
  val convert
    : Abt.metactx * Abt.metavariable NameEnv.dict
    -> Ast.ast * Abt.sort
    -> Abt.abt

  (* convert an open ast to an abt *)
  val convertOpen
    : Abt.metactx * Abt.metavariable NameEnv.dict
    -> Abt.symbol NameEnv.dict * Abt.variable NameEnv.dict
    -> Ast.ast * Abt.sort
    -> Abt.abt
end
