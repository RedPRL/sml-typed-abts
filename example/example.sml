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

    datatype operator = LAM of int | AP of int | NUM | LIT of int | RET
    type 'i t = operator

    functor Eq (I : EQ) =
    struct
      type t = operator
      fun eq (x:t, y) = x = y
    end

    functor Show (I : SHOW) =
    struct
      type t = operator
      fun toString (LAM i) = "lam"
        | toString (AP i) = "ap"
        | toString NUM = "#"
        | toString (LIT n) = Int.toString n
        | toString RET = "ret"
    end

    fun ->> (rho, tau) = (rho, tau)
    infixr ->>

    fun c x = [] ->> x

    local
      open Sort
      fun replicate i x = List.tabulate (i, fn _ => x)
    in
      fun arity (LAM i) = [replicate i EXP ->> EXP] ->> VAL
        | arity RET = [c VAL] ->> EXP
        | arity (AP i) = replicate (i + 1) (c EXP) ->> EXP
        | arity NUM = [c NAT] ->> VAL
        | arity (LIT _) = c NAT

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

  structure Eval =
  struct
    fun eval e =
      let
        val ((_, sigma), pat) = infer e
      in
        case pat of
             `x => raise Fail "free variable"
           | _ \ _ => raise Fail "unexpected binding"
           | LAM i $ _ => e
           | RET $ _ => e
           | AP i $ es =>
               let
                 fun go (m :: []) = eval m
                   | go (m :: es) =
                     let
                       val ((_, tau), RET $ [m']) = infer (eval m)
                       val (_, LAM i $ [xsE]) = infer m'
                       val (_, xs \ E) = infer xsE
                       val i' = Int.min (i, List.length es)
                       val es1 = List.take (es, i')
                       val es2 = List.drop (es, i')
                       val j = List.length es2
                       val E' =
                         ListPair.foldr
                           (fn (x,e,mem) => subst (e,x) mem)
                           E
                           (xs, es1)
                     in
                       if j > 0 then
                         go (E'::es2)
                       else
                         eval E'
                     end
                   | go _ = raise Match
               in
                 go es
               end
           | _ => raise Match
      end
  end

  val $$ = STAR o op$
  infix 5 $$

  val \\ = STAR o op\
  infixr 4 \\

  val `` = STAR o `
  val a = V.named "a"
  val b = V.named "b"

  fun lam xs e = LAM (List.length xs) $$ [xs \\ e]
  fun ap es = AP (List.length es - 1) $$ es
  fun ret x = RET $$ [x]
  fun num x = NUM $$ [x]
  fun lit n = LIT n $$ []

  (* Two different implementations of const; one with multiabstraction, and
   * another with iterated abstraction. *)
  val const = lam [a,b] (``a)
  val const' = lam [a] (ret (lam [b] (``a)))

  val expr1 = checkStar (ap [ret const, ret (num (lit 1)), ret (num (lit 23))], c EXP)
  val expr2 = checkStar (ap [ret const', ret (num (lit 1)), ret (num (lit 23))], c EXP)

  val _ = print (ShowAbt.toString (Eval.eval expr1) ^ " == " ^ ShowAbt.toString (Eval.eval expr2) ^ "\n")
end
