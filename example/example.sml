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

    datatype 'i t =
        LAM | AP | NUM | LIT of int | RET
      | DECL | GET of 'i | SET of 'i

    functor Eq (I : EQ) =
    struct
      type t = I.t t
      fun eq (LAM, LAM) = true
        | eq (AP, AP) = true
        | eq (NUM, NUM) = true
        | eq (LIT m, LIT n) = m = n
        | eq (RET, RET) = true
        | eq (DECL, DECL) = true
        | eq (GET i, GET j) = I.eq (i, j)
        | eq (SET i, SET j) = I.eq (i, j)
        | eq _ = false
    end

    functor Show (I : SHOW) =
    struct
      type t = I.t t
      fun toString LAM = "lam"
        | toString AP = "ap"
        | toString NUM = "#"
        | toString (LIT n) = Int.toString n
        | toString RET = "ret"
        | toString DECL = "∇"
        | toString (GET i) = "get[" ^ I.toString i ^ "]"
        | toString (SET i) = "set[" ^ I.toString i ^ "]"
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
        | arity DECL = ([mkValence [] [] EXP, mkValence [EXP] [] EXP], EXP)
        | arity (GET _) = ([], EXP)
        | arity (SET _) = ([mkValence [] [] EXP], EXP)

      fun proj theta = ([], arity theta)
    end

    structure Renaming =
    struct
      type 'i t = 'i t
      fun map f LAM = LAM
        | map f AP = AP
        | map f NUM = NUM
        | map f (LIT n) = LIT n
        | map f RET = RET
        | map f DECL = DECL
        | map f (GET i) = GET (f i)
        | map f (SET i) = SET (f i)
    end
  end

  structure Abt = AbtUtil(Abt (structure Operator = O and Variable = V and Symbol = I))
  structure ShowAbt = PlainShowAbt (Abt)
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

  val u = I.named "u"


  fun mkValence p q s = ({symbols = p, variables = q}, s)
  val n1 = RET $$ [NUM $$ [LIT 1 $$ []]]
  val expr1 =
    checkStar
      (DECL $$ [``a, ([u], []) \\ GET u $$ []],
       mkValence [] [] EXP)

  val _ = print ("\n\n" ^ ShowAbt.toString expr1 ^ "\n\n")
end
