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

    structure Arity = Arity (structure Sort = Sort and Spine = ListSpine)

    datatype operator = LAM of int | AP of int | NUM | LIT of int | RET
    type t = operator

    fun eq (x:t, y) = x = y
    fun toString (LAM i) = "lam"
      | toString (AP i) = "ap"
      | toString NUM = "num"
      | toString (LIT n) = Int.toString n
      | toString RET = "ret"

    fun ->> (rho, tau) = (rho, tau)
    infixr ->>

    fun c x = [] ->> x

    local
      open Sort
      fun replicate 0 x = []
        | replicate i x =
            if i < 0 then
              raise Match
            else
              x :: replicate (i - 1) x
    in
      fun arity (LAM i) = [replicate i EXP ->> EXP] ->> VAL
        | arity RET = [c VAL] ->> EXP
        | arity (AP i) = replicate i (c EXP) ->> EXP
        | arity NUM = [c NAT] ->> VAL
        | arity (LIT _) = c NAT
    end
  end

  structure Abt = AbtUtil(Abt (structure Operator = O and Variable = V))
  structure ShowAbt = PlainShowAbt (Abt)
  open O O.Sort Abt


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

  val expr = LAM 3 $$ [[f,g,h] \\ AP 3 $$ [``f,``g,``h]]
  val example = checkStar (expr, c VAL)
  val _ = print (ShowAbt.toString example ^ "\n")
end
