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

    structure Arity = Arity (Sort)

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
        | arity AP = [c EXP, c EXP] ->> EXP
        | arity NUM = [c NAT] ->> VAL
        | arity ZE = c NAT
        | arity SU = [c NAT] ->> NAT
    end
  end

  structure Abt = AbtUtil(Abt (structure Operator = O and Variable = V))
  structure ShowAbt = ShowAbt (Abt)
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
  val example = checkStar (LAM 2 $$ [[f,g] \\ AP $$ [``f, ``g]],  c VAL)
  val _ = print (ShowAbt.toString example ^ "\n")
end
