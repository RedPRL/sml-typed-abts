structure Example =
struct
  structure M = Symbol ()
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

    fun eq f (LAM, LAM) = true
      | eq f (AP, AP) = true
      | eq f (NUM, NUM) = true
      | eq f (LIT m, LIT n) = m = n
      | eq f (RET, RET) = true
      | eq f (DECL, DECL) = true
      | eq f (GET i, GET j) = f (i, j)
      | eq f (SET i, SET j) = f (i, j)
      | eq _ _ = false

    fun toString f LAM = "lam"
      | toString f AP = "ap"
      | toString f NUM = "#"
      | toString f (LIT n) = Int.toString n
      | toString f RET = "ret"
      | toString f DECL = "decl"
      | toString f (GET i) = "get[" ^ f i ^ "]"
      | toString f (SET i) = "set[" ^ f i ^ "]"

    local
      open Sort
      fun replicate i x = List.tabulate (i, fn _ => x)
      fun mkValence p q s = ((p, q), s)
    in
      fun arity LAM = ([mkValence [] [EXP] EXP], EXP)
        | arity RET = ([mkValence [] [] VAL], EXP)
        | arity AP = ([mkValence [] [] EXP, mkValence [] [] EXP], EXP)
        | arity NUM = ([mkValence [] [] NAT], VAL)
        | arity (LIT _) = ([], NAT)
        | arity DECL = ([mkValence [] [] EXP, mkValence [EXP] [] EXP], EXP)
        | arity (GET i) = ([], EXP)
        | arity (SET i) = ([mkValence [] [] EXP], EXP)

      fun support (GET i) = [(i, EXP)]
        | support (SET i) = [(i, EXP)]
        | support _ = []
    end

    structure Presheaf =
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

  structure MC = Metacontext (structure Metavariable = M type valence = O.Arity.Valence.t)

  structure Abt = AbtUtil(Abt (structure Operator = O and Metavariable = M and Metacontext = MC and Variable = V and Symbol = I))
  structure ShowAbt = PlainShowAbt (Abt)
  open O O.Sort Abt

  infixr 4 \
  infix 5 $

  val $$ = STAR o op$
  val $$# = STAR o op$#
  infix 5 $$ $$#

  val `` = STAR o `
  val a = V.named "a"
  val u = I.named "u"
  val mv = M.named "m"
  val mvap = mv $$# ([], [])
  val Theta = MC.extend MC.empty (mv, (([], []), EXP))

  fun K x = ([], []) \ x

  val expr1 =
    checkStar
      Theta
      (DECL $$ [K mvap, ([u], []) \ GET u $$ []])
      EXP
  val _ = print ("\n\n" ^ ShowAbt.toString expr1 ^ "\n\n")
end
