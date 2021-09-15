structure Sort =
struct
  datatype t = EXP | NAT
  val eq : t * t -> bool = op=
  fun toString EXP = "exp"
    | toString NAT = "nat"
end

structure O =
struct
  structure Ar = ListAbtArity (structure S = Sort)
  datatype t = LAM | AP | NUM | LIT of int

  val eq : t * t -> bool = op=
  val toString =
    fn LAM => "lam"
     | AP => "ap"
     | NUM => "num"
     | LIT n => Int.toString n

  local
    open Sort
    fun mkValence q s = (q, s)
  in
    val arity =
      fn LAM => ([mkValence [EXP] EXP], EXP)
       | AP => ([mkValence [] EXP, mkValence [] EXP], EXP)
       | NUM => ([mkValence [] NAT], EXP)
       | LIT _ => ([], NAT)
  end
end

structure Operator = O

structure AbtKit =
struct
  structure O = Operator
    and Metavar = AbtSymbol ()
    and Var = AbtSymbol ()
  type annotation = Pos.t
end

structure Abt = Abt (AbtKit)
structure ShowAbt = DebugShowAbt (Abt)

structure AstKit =
struct
  structure Operator = Operator
  type annotation = Pos.t
end

structure Ast = AstUtil (Ast (AstKit))
structure AstToAbt = AstToAbt (structure Abt = Abt and Ast = Ast)
