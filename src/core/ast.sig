signature AST =
sig
  type operator

  type variable = string
  type metavariable = string

  type annotation
  type ast

  datatype 'a view =
      ` of variable
    | $ of operator * 'a abs list
    | $# of metavariable * 'a list
  and 'a abs = \ of variable list * 'a

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
  val $$ : operator * ast abs list -> ast
  val $$# : metavariable * ast list -> ast
end

signature AST_ABT =
sig
  structure Abt : ABT
  structure Ast : AST

  sharing type Ast.operator = Abt.O.t
  sharing type Ast.annotation = Abt.annotation
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
    -> Abt.variable NameEnv.dict
    -> Ast.ast * Abt.sort
    -> Abt.abt
end
