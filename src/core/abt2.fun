functor Abt2
  (structure Var : ABT_SYMBOL
   structure Metavar : ABT_SYMBOL
   structure O : ABT_OPERATOR
   type annotation) : ABT =
struct
  exception todo
  fun ?e = raise e

  structure Var = Var and Metavar = Metavar and O = O

  structure S = O.Ar.Vl.S and Valence = O.Ar.Vl
  structure MetaCtxUtil = ContextUtil (structure Ctx = Metavar.Ctx and Elem = Valence)
  structure VarCtxUtil = ContextUtil (structure Ctx = Var.Ctx and Elem = S)

  type sort = O.Ar.Vl.S.t

  datatype 'a locally =
     FREE of 'a
   | BOUND of int

  type variable = Var.t
  type metavariable = Metavar.t
  type operator = O.t
  type valence = O.Ar.valence
  type varctx = sort Var.Ctx.dict
  type metactx = valence Metavar.Ctx.dict

  exception SortError of {annotation: annotation option, description: string}

  structure Views = AbtViews
  open Views

  type 'a view = (variable, metavariable, operator, 'a) termf
  type 'a bview = (variable, 'a) bindf
  type 'a appview = (variable, operator, 'a) appf

  datatype 'a scope = <\> of string option list * 'a

  infixr 5 \
  infix 5 $ $# <\>

  type annotation = annotation


  datatype 'a annotated = <: of 'a * annotation option
  infix 4 <:


  datatype abt_repr =
     V of var_term
   | APP of app_term
   | META of meta_term
  and abs = ABS of sort list * abt scope
  and abt_susp = DEFER of abt_repr * task Queue.queue

  and task =
      SUBST_VARS of varenv
    | RENAME_VARS of variable Var.Ctx.dict
    | SUBST_METAS of metaenv
    | RENAME_METAS of metavariable Metavar.Ctx.dict

  withtype abt = abt_susp annotated ref

  and var_term = Var.t locally * sort
  and app_term = O.t * abs list
  and meta_term = (Metavar.t * sort) * abt list
  and metaenv = abs Metavar.Ctx.dict
  and varenv = abt Var.Ctx.dict

  fun @@ (f, x) = f x
  infixr @@




  fun assertSortEq ann (sigma, tau) =
    if S.eq (sigma, tau) then () else
      raise SortError
        {annotation = ann,
         description = "Sort Error: expected " ^ S.toString sigma ^ ", but got " ^ S.toString tau}

  fun primMapAbs f (ABS (taus, xs <\> bdy)) =
    ABS (taus, xs <\> f bdy)

  fun <+> (m1, m2) =
    case m1 of
       NONE => m2
     | SOME x => m1

  infixr <+>

  fun abtAppendTasks tasks abt =
    let
      val DEFER (repr, tasks') <: ann = !abt
      fun go out q =
        if Queue.isEmpty q then out else
        let
          val (a, q') = Queue.front q
        in
          go (Queue.insert out a) q'
        end

      val tasks'' = go tasks' tasks
    in
      ref @@ DEFER (repr, tasks'') <: ann
    end

  fun evalAbt n abt tasks : abt_repr annotated =
    let
      val DEFER (repr, tasks') <: ann = !abt
      val repr' <: ann' = evalRepr n repr tasks' ann
    in
      abt := DEFER (repr', Queue.empty) <: ann';
      evalRepr n repr' tasks ann'
    end

  and evalRepr n repr tasks ann =
    if Queue.isEmpty tasks then repr <: ann else
    case repr of
       V (FREE x, tau) =>
       (evalVar n x tau tasks
        handle Queue.Empty => repr <: ann)
     | V (BOUND _, _) =>
       repr <: ann
     | APP (theta, abss) =>
       APP (theta, List.map (primMapAbs (abtAppendTasks tasks)) abss) <: ann
     | META ((X, tau), abts) =>
       let
         val reprs = List.map (fn abt => evalAbt n abt tasks) abts
       in
         evalMeta n X tau reprs tasks
         handle Queue.Empty => repr <: ann
       end

  and evalVar n x tau tasks =
    case Queue.front tasks of
       (SUBST_VARS rho, tasks) =>
       (case Var.Ctx.find rho x of
           NONE => evalVar n x tau tasks
         | SOME abt => evalAbt n abt tasks)
     | (RENAME_VARS rho, tasks) =>
       (case Var.Ctx.find rho x of
           NONE => evalVar n x tau tasks
         | SOME y => evalVar n y tau tasks)
     | (_, tasks) => evalVar n x tau tasks

  and evalMeta n X tau reprs tasks =
    case Queue.front tasks of
       (SUBST_METAS rho, tasks) =>
       (case Metavar.Ctx.find rho X of
           NONE => evalMeta n X tau reprs tasks
         | SOME abs => evalAbt n (instAbs n reprs abs) tasks)
     | (RENAME_METAS rho, tasks) =>
       (case Metavar.Ctx.find rho X of
           NONE => evalMeta n X tau reprs tasks
         | SOME Y => evalMeta n Y tau reprs tasks)
     | (_, tasks) => evalMeta n X tau reprs tasks

  and instAbs (n : int) reprs abs =
    let
      val ABS (taus, _ <\> abt) = abs
      val len = List.length reprs

      fun go n (abt : abt) : abt =
        let
          val repr <: ann = evalAbt n abt Queue.empty
          val repr' <: ann' = goRepr n (repr <: ann)
        in
          ref @@ DEFER (repr', Queue.empty) <: ann'
        end

      and goRepr n (repr <: ann) =
        case repr of
           V (BOUND i, _) =>
           let
             val j = i - n
           in
             if j >= 0 andalso j < len then List.nth (reprs, j) else repr <: ann
           end
         | V (FREE _, _) =>
           repr <: ann
         | META ((X, tau), abts) =>
           META ((X, tau), List.map (go n) abts) <: ann
         | APP (th, abss) =>
           APP (th, List.map (goAbs n) abss) <: ann

      and goAbs n (abs : abs) : abs =
        let
          val ABS (taus, xs <\> abt) = abs
          val n' = n + List.length taus
        in
          ABS (taus, xs <\> go n' abt)
        end
    in
      (* Check if reprs needs to be reversed... *)
      go n abt
    end



  fun sort_ n abt =
    case evalAbt n abt Queue.empty of
       V (_, tau) <: _ => tau
     | APP (theta, _) <: _ => #2 (O.arity theta)
     | META ((_, tau), _) <: _ => tau

  val sort = sort_ 0

  fun indexOfFirst pred xs =
    let
      fun aux (i, []) = NONE
        | aux (i, x::xs) = if pred x then SOME i else aux (i + 1, xs)
    in
      aux (0, xs)
    end


  fun closeVariables (xs : variable list) : abt -> abt =
    let
      fun go n xs (abt : abt) : abt =
        let
          val repr <: ann = evalAbt n abt Queue.empty
          val repr' <: ann' = goRepr n xs (repr <: ann)
        in
          ref @@ DEFER (repr', Queue.empty) <: ann'
        end

      and goRepr n xs (repr <: ann) =
        case repr of
           V (BOUND _, _) => repr <: ann
         | V (FREE x, tau) =>
           (case indexOfFirst (fn y => Var.eq (x, y)) xs of
               NONE => repr <: ann
             | SOME i => V (BOUND @@ i + n, tau) <: ann)
         | META ((X, tau), abts) => META ((X, tau), List.map (go n xs) abts) <: ann
         | APP (th, abss) => APP (th, List.map (goAbs n xs) abss) <: ann

      and goAbs n xs abs = 
        let
          val ABS (taus, ys <\> abt) = abs
          val n' = n + List.length taus
        in
          ABS (taus, ys <\> go n' xs abt)
        end
    in
      (* Somehow it seems like xs need to be reversed, but that wouldn't match the old implementation. what gives? *)
      go 0 xs
    end

  fun metactx abt = 
    let
      fun go n ctx abt =
        case evalAbt n abt Queue.empty of 
           V _ <: _ => ctx
         | APP (_, abss) <: _ => List.foldl (fn (abs, ctx) => goAbs n ctx abs) ctx abss
         | META ((X, tau), abts) <: _ =>
           let
             val taus = List.map (sort_ n) abts
             val ctx' = Metavar.Ctx.insert ctx X (taus, tau)
           in
             List.foldl (fn (abt, ctx) => go n ctx abt) ctx' abts
           end
      and goAbs n ctx abs = 
        let
          val ABS (taus, _ <\> abt) = abs
          val n' = n + List.length taus
        in
          go n' ctx abt
        end
    in
      go 0 Metavar.Ctx.empty abt
    end 

  fun varctx abt = 
    let
      fun go n ctx abt =
        case evalAbt n abt Queue.empty of 
           V (FREE x, tau) <: _ => Var.Ctx.insert ctx x tau
         | V _ <: _ => ctx
         | APP (_, abss) <: _ => List.foldl (fn (abs, ctx) => goAbs n ctx abs) ctx abss
         | META (_, abts) <: _ =>
           List.foldl (fn (abt, ctx) => go n ctx abt) ctx abts
      and goAbs n ctx abs = 
        let
          val ABS (taus, _ <\> abt) = abs
          val n' = n + List.length taus
        in
          go n' ctx abt
        end
    in
      go 0 Var.Ctx.empty abt
    end


  fun unbind abs abts : abt =
    let
      val reprs = List.map (fn abt => evalAbt 0 abt Queue.empty) abts
    in
      instAbs 0 reprs abs
    end

  fun // (abs,  ms) =
    unbind abs ms

  infix //

  fun substMetaenv (env : metaenv) abt =
    let
      val DEFER (repr, tasks) <: ann = !abt
    in
      ref @@ DEFER (repr, Queue.insert tasks @@ SUBST_METAS env) <: ann
    end

  fun substVarenv (env : varenv) abt =
    let
      val DEFER (repr, tasks) <: ann = !abt
    in
      ref @@ DEFER (repr, Queue.insert tasks @@ SUBST_VARS env) <: ann
    end

  fun renameVars env abt =
    let
      val DEFER (repr, tasks) <: ann = !abt
    in
      ref @@ DEFER (repr, Queue.insert tasks @@ RENAME_VARS env) <: ann
    end

  fun renameMetavars env abt =
    let
      val DEFER (repr, tasks) <: ann = !abt
    in
      ref @@ DEFER (repr, Queue.insert tasks @@ RENAME_METAS env) <: ann
    end


  fun makePureAbt repr =
    ref @@ DEFER (repr, Queue.empty) <: NONE

  fun check (view, tau) : abt =
    case view of
       `x =>
       makePureAbt @@ V (FREE x, tau)

     | X $# abts =>
       makePureAbt @@ META ((X, tau), abts)

     | theta $ bs =>
       let
         val (vls, tau') = O.arity theta
         val _ = assertSortEq NONE (tau, tau')
         val abss = ListPair.mapEq checkb (bs, vls)
       in
         makePureAbt @@ APP (theta, abss)
       end

    and checkb (xs \ abt, vl) : abs =
      let
        val (taus, tau) = vl
        val names = List.map Var.name xs
        val bdy = closeVariables xs abt
        val scope = names <\> bdy
      in
        ABS (taus, scope)
      end

  fun infer abt : abt view * sort =
    case evalAbt 0 abt Queue.empty of
       V (FREE x, tau) <: _ =>
       (`x, tau)

     | META ((X, tau), abts) <: _ =>
       (X $# abts, tau)

     | APP (theta, abss) <: _ =>
       let
         val (_, tau) = O.arity theta
         val bs = List.map outb abss
       in
         (theta $ bs, tau)
       end


  and inferb abs : abt bview * valence =
    let
      val ABS (taus, names <\> abt) = abs
      val tau = sort abt
      val xs = List.map (fn SOME x => Var.named x | NONE => Var.new ()) names
      val vars = ListPair.mapEq (fn (x, tau) => V (FREE x, tau) <: NONE) (xs, taus)
      val abt' = instAbs 0 vars abs
    in
      (xs \ abt', (taus, tau))
    end

  and outb abs : abt bview = #1 (inferb abs)

  fun valence abs =
    let
      val ABS (taus, _ <\> abt) = abs
      val tau = sort abt
    in
      (taus, tau)
    end





  fun locallyToString f =
    fn FREE x => f x
     | BOUND i => "<" ^ Int.toString i ^ ">"

  fun prettyList f l c r xs =
    case xs of
       [] => ""
     | _ => l ^ ListUtil.joinWith f c xs ^ r

  fun primVarToString xs =
    fn FREE x => Var.toString x
     | BOUND i =>
          if i < List.length xs then
            "!" ^
              (case List.nth (xs, List.length xs - i - 1) of
                  SOME s => s
                | NONE => "?")
          else
            "%" ^ Int.toString i

  local
    fun primToString' xs abt =
      case evalAbt 0 abt Queue.empty of
         V (v, _) <: _ => primVarToString xs v
       | APP (theta, abss) <: _ =>
         O.toString theta ^ prettyList (primToStringAbs' xs) "(" "; " ")" abss
       | META ((X, _), abts) <: _ =>
         "#" ^ Metavar.toString X ^ prettyList (primToString' xs) "[" ", " "]" abts

    and primToStringAbs' xs =
      fn ABS ([], _ <\> abt) => primToString' xs abt
       | ABS (taus, xs' <\> abt) =>
         prettyList (fn SOME x => x | NONE => "?") "[" ", " "]" xs' ^ "." ^ primToString' (xs @ xs') abt
  in
    fun primToString t = primToString' [] t
    fun primToStringAbs t = primToStringAbs' [] t
  end

  fun varOccurrences abt : annotation list Var.Ctx.dict =
    let
      fun go n occs abt = 
        case evalAbt n abt Queue.empty of 
           V (FREE x, _) <: SOME ann =>
           #3 @@ Var.Ctx.operate occs x (fn _ => [ann]) (fn anns => ann :: anns)
         | V _ <: _ => occs
         | META (_, abts) <: _ => List.foldl (fn (abt, occs) => go n occs abt) occs abts
         | APP (_, abss) <: _ => List.foldl (fn (abs, occs) => goAbs n occs abs) occs abss
      and goAbs n occs abs = 
        let
          val ABS (taus, _ <\> abt) = abs
          val n' = n + List.length taus
        in
          go n' occs abt
        end
    in
      go 0 Var.Ctx.empty abt
    end

  fun substVar (m, x) =
    substVarenv (Var.Ctx.singleton x m)

  fun annotate ann abt =
    let
      val DEFER (repr, tasks) <: _ = !abt
    in
      ref @@ DEFER (repr, tasks) <: SOME ann
    end

  fun getAnnotation abt = 
    let
      val DEFER (_, _) <: ann = !abt
    in
      ann
    end

  fun setAnnotation ann abt =
    let
      val DEFER (repr, tasks) <: _ = !abt
    in
      ref @@ DEFER (repr, tasks) <: ann
    end

  fun clearAnnotation abt = 
    let
      val DEFER (repr, tasks) <: _ = !abt
    in
      ref @@ DEFER (repr, tasks) <: NONE
    end

  fun metavar (X, (taus, tau)) =
    let
      fun aux f i names results sorts =
        case sorts of
           [] => (List.rev names, List.rev results)
         | sort::sorts =>
           let
             val r = f (i, sort)
           in
             aux f (i + 1) (SOME ("?" ^ Int.toString i) :: names) (r :: results) sorts
           end

      val (xs, abts) = aux (fn (i, tau) => makePureAbt @@ V (BOUND i, tau)) 0 [] [] taus
      val body = makePureAbt @@ META ((X, tau), abts)
    in
      ABS (taus, xs <\> body)
    end



  fun out abt = #1 (infer abt)

  fun $$ (theta, args) =
    check (theta $ args, #2 (O.arity theta))

  fun locallyEq f =
    fn (FREE x, FREE y) => f (x, y)
     | (BOUND i, BOUND j) => i = j
     | _ => false

  fun eq_ n (abt1, abt2) =
    if abt1 = abt2 then true else
    case (evalAbt n abt1 Queue.empty, evalAbt n abt2 Queue.empty) of 
       (V (x0, _) <: _, V (x1, _) <: _) =>
       locallyEq Var.eq (x0, x1)
     | (APP (th0, abss0) <: _, APP (th1, abss1) <: _) =>
       O.eq (th0, th1) andalso ListPair.allEq (eqAbs_ n) (abss0, abss1)
     | (META ((X0,_), abts0) <: _, META ((X1,_), abts1) <: _) =>
       Metavar.eq (X0, X1) andalso ListPair.allEq (eq_ n) (abts0, abts1)

  and eqAbs_ n (abs0 : abs, abs1 : abs) : bool =
    let
      val ABS (taus0, _ <\> abt0) = abs0
      val ABS (_, _ <\> abt1) = abs1
      val n' = n + List.length taus0
    in
      eq_ n' (abt0, abt1)
    end


  val eq = eq_ 0
  val eqAbs = eqAbs_ 0

  fun mapAbs f abs =
    let
      val (xs \ m, vl) = inferb abs
    in
      checkb (xs \ f m, vl)
    end

  fun abtToAbs abt = ABS ([], [] <\> abt)

  fun inheritAnnotation t1 t2 =
    case getAnnotation t2 of
        NONE => setAnnotation (getAnnotation t1) t2
      | _ => t2

  fun mapSubterms f m =
    let
      val (view, tau) = infer m
    in
      setAnnotation (getAnnotation m) (check (map f view, tau))
    end

  fun deepMapSubterms f m =
    mapSubterms (f o deepMapSubterms f) m

  fun substMetavar (scope, X) =
    substMetaenv (Metavar.Ctx.singleton X scope)

end

functor SimpleAbt (O : ABT_OPERATOR) =
  Abt (structure Sym = AbtSymbol ()
       structure Var = AbtSymbol ()
       structure Metavar = AbtSymbol ()
       structure O = O
       type annotation = unit)
