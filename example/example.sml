structure Example =
struct
  structure V = Variable ()
  structure O =
  struct
    structure Sort =
    struct
      datatype sort = EXP | VAL | NAT
      type t = sort
      val eq : sort * sort -> bool = op=
      fun toString EXP = "exp"
        | toString VAL = "val"
        | toString NAT = "nat"
    end

    structure R = RoseTree
    structure RoseTreeSpine = RoseTreeSpine (R)
    structure Arity = Arity (structure Sort = Sort and Spine = RoseTreeSpine)

    datatype operator = LAM of int | AP | NUM | ZE | SU | RET
    type t = operator

    fun eq (x:t, y) = x = y
    fun toString (LAM i) = "lam"
      | toString AP = "ap"
      | toString NUM = "num"
      | toString ZE = "ze"
      | toString SU = "su"
      | toString RET = "ret"

    fun ->> (rho, tau) = (rho, tau)
    infixr ->>

    fun c x = R.NIL ->> x

    local
      open Sort
      fun replicate 0 x = []
        | replicate i x =
            if i < 0 then
              raise Match
            else
              x :: replicate (i - 1) x

      fun multiplex 0 x = R.NIL
        | multiplex i x =
            if i < 0 then
              raise Match
            else
              R.@^ (x, replicate i (multiplex (i - 1) x))
    in
      val op@^ = R.@^
      infix 4 @^
      fun arity (LAM i) = ((multiplex i EXP ->> EXP) @^ []) ->> VAL
        | arity RET = c VAL @^ [] ->> EXP
        | arity AP = c EXP @^ [c EXP @^ []] ->> EXP
        | arity NUM = c NAT @^ [] ->> VAL
        | arity ZE = c NAT
        | arity SU = c NAT @^ [] ->> NAT
    end
  end

  structure Abt = AbtUtil(Abt (structure Operator = O and Variable = V))
  structure ShowAbt = DebugShowAbt (Abt)
  open O O.Sort Abt

  val op@^ = R.@^
  infix 6 @^

  infixr 5 \
  infix 5 $

  val $$ = STAR o op$
  infix 5 $$

  val \\ = STAR o op\
  infixr 4 \\

  val `` = STAR o `
  val f = V.named "f"
  val g = V.named "g"
  val h = V.named "h"

  val vars = f @^ [g @^ [R.NIL], h @^ [R.NIL]]

  val expr = LAM 2 $$ (vars \\ AP $$ (``f @^ [``g @^ []])) @^ []
  val example = checkStar (expr, c VAL)
  val _ = print (ShowAbt.toString example ^ "\n")
end
