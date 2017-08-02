functor SetUtil (S : SET) :
sig
  include SET

  exception Duplicate
  val insertDistinct : set -> elem -> set

  val fromList : elem list -> set
  val fromListDistinct : elem list -> set
end = 
struct
  open S
  exception Duplicate

  fun insertDistinct s e = 
    if member s e then 
      raise Duplicate
    else
      insert s e

  val fromList = List.foldl (fn (e, s) => insert s e) empty
  val fromListDistinct = List.foldl (fn (e, s) => insertDistinct s e) empty
end

functor Unify (Tm : ABT) :
sig
  type substitution = Tm.metaenv
  exception Unify of Tm.abt * Tm.abt

  val unify : substitution -> Tm.abt * Tm.abt -> substitution
end = 
struct
  open Tm
  type substitution = metaenv

  exception todo
  fun ?e = raise e
  fun @@ (f, x) = f x

  infix 0 @@
  infix 1 \
  infix 2 $ $# $$

  exception Unify of abt * abt

  structure Syms = SetUtil (SplaySet (structure Elem = Sym.Ord))
  structure Vars = SetUtil (SplaySet (structure Elem = Var.Ord))

  exception Pattern
  exception Occurs
  exception Unbound
  exception Sort

  local
    val counter = ref 0
  in
    fun freshMeta () = 
      let
        val i = !counter
      in
        counter := i + 1;
        Metavar.named @@ "pat" ^ Int.toString i
      end
  end

  fun asSymbol r = 
    case r of 
       O.P.VAR u => u
     | _ => raise Pattern

  fun asVariable tm = 
    case out tm of
       `x => x
     | _ => raise Pattern

  val paramsToSymbols : (param * psort) list -> symbol list =
    List.map (asSymbol o #1)
  
  val termsToVariables : abt list -> variable list = 
    List.map asVariable

  fun proj (syms, vars) rho tm =
    let
      val tm' = substMetaenv rho tm
      val tau = sort tm'
    in
      case out tm' of 
         `x => if Vars.member vars x then rho else raise Unbound
       | _ $ bs => List.foldl (fn (b, rho) => projb (syms, vars) rho b) rho bs
       | X $# (rs, tms) =>
         let
           val us = paramsToSymbols rs
           val xs = termsToVariables tms

           val syms' = Syms.fromListDistinct us handle Syms.Duplicate => raise Pattern
           val vars' = Vars.fromListDistinct xs handle Vars.Duplicate => raise Pattern
         in
           if Syms.subset (syms', syms) andalso Vars.subset (vars', vars) then
             rho
           else
             let
               val Y = freshMeta ()
               val rs' = List.mapPartial (fn r as (O.P.VAR u, sigma) => if Syms.member syms u then SOME r else NONE | _ => NONE) rs
               val tms' = List.mapPartial (fn tm => case out tm of `x => if Vars.member vars x then SOME tm else NONE | _ => NONE) tms
               val bnd = (us, xs) \ check (Y $# (rs', tms'), tau)
               val vl = ((List.map #2 rs, List.map sort tms), tau)
             in
               Metavar.Ctx.insert rho X @@ checkb (bnd, vl)
             end
         end
    end
  and projb (syms, vars) rho ((us, xs) \ tm) =
    let
      val syms' = Syms.union syms @@ Syms.fromList us
      val vars' = Vars.union vars @@ Vars.fromList xs
    in
      proj (syms', vars') rho tm
    end

  fun flexRigid rho (X : metavariable, tau, rs : (param * psort) list, tms, t : abt) : substitution =
    if Metavar.Ctx.member (metactx t) X then 
      raise Occurs
    else
      let
        val us = paramsToSymbols rs
        val xs = termsToVariables tms
        val vl = ((List.map #2 rs, List.map sort tms), tau)
        val rho' = Metavar.Ctx.insert rho X @@ checkb ((us, xs) \ t, vl)
      in
        proj (Syms.fromListDistinct us, Vars.fromListDistinct xs) rho' t
          handle Syms.Duplicate => raise Pattern
               | Vars.Duplicate => raise Pattern
      end


  fun flexFlex1 rho (X, tau, rs1, rs2, tms1, tms2) =
    let
      val us1 = paramsToSymbols rs1
      val us2 = paramsToSymbols rs2
      val xs1 = termsToVariables tms1
      val xs2 = termsToVariables tms2
    in
      if ListPair.allEq Var.eq (xs1, xs2) andalso ListPair.allEq Sym.eq (us1, us2) then 
        rho
      else
        let
          val Y = freshMeta ()
          val rs' = ListPair.mapPartialEq (fn ((r1, sigma1), (r2, sigma2)) => if O.P.eq Sym.eq (r1, r2) andalso O.Ar.Vl.PS.eq (sigma1, sigma2) then SOME (r1, sigma1) else NONE) (rs1, rs2)
          val tms' = ListPair.mapPartialEq (fn (tm1, tm2) => if Tm.eq (tm1, tm2) then SOME tm1 else NONE) (tms1, tms2)
          val bnd = (us1, xs1) \ check (Y $# (rs', tms'), tau)
          val vl = ((List.map #2 rs1, List.map sort tms1), tau)
        in
          Metavar.Ctx.insert rho X @@ checkb (bnd, vl)
        end
    end

  fun flexFlex2 rho (X1, X2, tau, rs1, rs2, tms1, tms2) =
    let
      val us1 = paramsToSymbols rs1
      val us2 = paramsToSymbols rs2
      val xs1 = termsToVariables tms1
      val xs2 = termsToVariables tms2

      val syms1 = Syms.fromListDistinct us1 handle Syms.Duplicate => raise Pattern
      val syms2 = Syms.fromListDistinct us2 handle Syms.Duplicate => raise Pattern
      val vars1 = Vars.fromListDistinct xs1 handle Vars.Duplicate => raise Pattern
      val vars2 = Vars.fromListDistinct xs1 handle Vars.Duplicate => raise Pattern

      val vl1 = ((List.map #2 rs1, List.map sort tms1), tau)
      val vl2 = ((List.map #2 rs2, List.map sort tms2), tau)
    in
      if Syms.subset (syms1, syms2) andalso Vars.subset (vars1, vars2) then
        let
          val bnd = (us2, xs2) \ check (X1 $# (rs1, tms1), tau)
        in
          Metavar.Ctx.insert rho X2 @@ checkb (bnd, vl2)
        end
      else if Syms.subset (syms2, syms1) andalso Vars.subset (vars2, vars1) then 
        let
          val bnd = (us1, xs1) \ check (X2 $# (rs2, tms2), tau)
        in
          Metavar.Ctx.insert rho X1 @@ checkb (bnd, vl1)
        end
      else
        let
          val X3 = freshMeta ()
          val rs' = List.mapPartial (fn r as (O.P.VAR u, sigma) => if Syms.member syms2 u then SOME r else NONE | _ => NONE) rs1
          val tms' = List.mapPartial (fn tm => case out tm of `x => if Vars.member vars2 x then SOME tm else NONE | _ => NONE) tms1
          val tm = check (X3 $# (rs', tms'), tau)
          val bnd1 = (us1, xs1) \ tm
          val bnd2 = (us2, xs2) \ tm
          val rho' = Metavar.Ctx.insert rho X2 @@ checkb (bnd2, vl2)
        in
          Metavar.Ctx.insert rho' X1 @@ checkb (bnd1, vl1)
        end
    end

  fun unify rho (tm1, tm2) =
    let
      val tm1' = substMetaenv rho tm1
      val tm2' = substMetaenv rho tm2
      fun fail () = raise Unify (tm1', tm2')

      val tau = sort tm1
      val _ = if O.Ar.Vl.S.eq (tau, sort tm2) then () else raise Sort
    in
      case (out tm1', out tm2') of
         (`x1, `x2) => if Var.eq (x1, x2) then rho else fail ()
       | (theta1 $ bs1, theta2 $ bs2) =>
         if O.eq Sym.eq (theta1, theta2) then
           ListPair.foldlEq (fn (b1, b2, rho) => unifyb rho (b1, b2)) rho (bs1, bs2)
         else
           fail ()
       | (X1 $# (rs1, tms1), X2 $# (rs2, tms2)) =>
         if Metavar.eq (X1, X2) then 
           flexFlex1 rho (X1, tau, rs1, rs2, tms1, tms2)
         else
           flexFlex2 rho (X1, X2, tau, rs1, rs2, tms1, tms2)
       | (X $# (rs, tms), _) => (flexRigid rho (X, sort tm1', rs, tms, tm2') handle _ => fail ())
       | (_, X $# (rs, tms)) => (flexRigid rho (X, sort tm1', rs, tms, tm1') handle _ => fail ())
       | _ => fail ()
    end

  and unifyb rho ((us1, xs1) \ tm1, (us2, xs2) \ tm2) =
    let
      val sren = ListPair.foldl (fn (u2, u1, ren) => Sym.Ctx.insert ren u2 @@ O.P.ret u1) Sym.Ctx.empty (us2, us1)
      val vren = ListPair.foldl (fn (x2, x1, ren) => Var.Ctx.insert ren x2 x1) Var.Ctx.empty (xs2, xs1)
      val tm2' = substSymenv sren @@ renameVars vren tm2
    in
      unify rho (tm1, tm2)
    end
end