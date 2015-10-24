structure Example =
struct
  structure V = Symbol ()
  structure I = Symbol ()

  structure O =
  struct
    structure Sort =
    struct
      datatype t = EXP | VAL | NAT

      structure Eq =
      struct
        type t = t
        val eq : t * t -> bool = op=
      end

      structure Show =
      struct
        type t = t
        fun toString EXP = "exp"
          | toString VAL = "val"
          | toString NAT = "nat"
      end
    end

    structure Arity = Arity (structure Sort = Sort and Spine = ListSpine)

    datatype operator = LAM | AP | NUM | LIT of int | RET
    type 'i t = operator

    functor Eq (I : EQ) =
    struct
      type t = operator
      fun eq (x:t, y) = x = y
    end

    functor Show (I : SHOW) =
    struct
      type t = operator
      fun toString LAM = "lam"
        | toString AP = "ap"
        | toString NUM = "#"
        | toString (LIT n) = Int.toString n
        | toString RET = "ret"
    end

    local
      open Sort
      fun replicate i x = List.tabulate (i, fn _ => x)
      fun mkValence p q s = ({symbols = p, variables = q}, s)
    in
      fun arity LAM = ([mkValence [] [EXP] EXP], EXP)
        | arity RET = ([mkValence [] [] VAL], EXP)
        | arity AP = ([mkValence [] [] EXP, mkValence [] [] EXP], EXP)
        | arity NUM = ([mkValence [] [] NAT], VAL)
        | arity (LIT _) = ([], NAT)

      fun proj theta = ([], arity theta)
    end

    structure Renaming =
    struct
      type 'i t = 'i t
      fun map f theta = theta
    end
  end

  structure Abt = AbtUtil(Abt (structure Operator = O and Variable = V and Symbol = I))
  structure ShowAbt = DebugShowAbt (Abt)
  open O O.Sort Abt

  infixr 5 \
  infix 5 $

  val $$ = STAR o op$
  infix 5 $$

  val \\ = STAR o op\
  infixr 4 \\

  val `` = STAR o `
  val a = V.named "a"
  val b = V.named "b"

end
