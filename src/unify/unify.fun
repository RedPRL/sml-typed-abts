functor AbtUnify (Tm : ABT) :
sig
  exception Unify of Tm.abt * Tm.abt

  structure Metas :
  sig
    include SET where type elem = Tm.metavariable
    val fromList : elem list -> set
  end

  (* Unify two terms with respect to a set of pattern variables, i.e. metavariables
     which shall be regarded as flexible. All other metavariables encountered will be
     regarded as rigid. *)
  val unify : Metas.set -> Tm.abt * Tm.abt -> Tm.metaenv
end =
struct
  open Tm

  exception todo
  fun ?e = raise e
  fun @@ (f, x) = f x

  infix 0 @@
  infix 1 \
  infix 2 $ $# $$

  exception Unify of abt * abt

  structure Syms = SetUtil (SplaySet (structure Elem = Sym.Ord))
  structure Vars = SetUtil (SplaySet (structure Elem = Var.Ord))
  structure Metas = SetUtil (SplaySet (structure Elem = Metavar.Ord))

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

  fun shallowSubstMetaenv rho tm = 
    case out tm of 
       X $# (rs, tms) =>
       (case Metavar.Ctx.find rho X of 
           SOME abs => shallowSubstMetaenv rho @@ unbind abs (List.map #1 rs) tms
         | NONE => tm)
     | _ => tm

  fun occursInTerm rho (X, tm) =
    case out tm of
       Y $# (rs, tms) =>
       Metavar.eq (X, Y) orelse
         (case Metavar.Ctx.find rho Y of 
             SOME abs => occursInTerm rho (X, unbind abs (List.map #1 rs) tms)
           | NONE => occursInTerms rho (X, tms))
     | _ $ bs => occursInBinders rho (X, bs)
     | _ => false
  and occursInBinder rho (X, _ \ tm) = occursInTerm rho (X, tm)
  and occursInTerms rho (X, tms) = List.exists (fn tm => occursInTerm rho (X, tm)) tms
  and occursInBinders rho (X, bs) = List.exists (fn b => occursInBinder rho (X, b)) bs

  fun proj (pvars, rho) (syms, vars) tm =
    let
      val tm' = shallowSubstMetaenv rho tm
      val tau = sort tm'
    in
      case out tm' of
         `x => rho
       | _ $ bs => List.foldl (fn (b, rho) => projb (pvars, rho) (syms, vars) b) rho bs
       | X $# (rs, tms) =>
         let
           val us = paramsToSymbols rs
           val xs = termsToVariables tms

           val syms' = Syms.fromListDistinct us handle Syms.Duplicate => raise Pattern
           val vars' = Vars.fromListDistinct xs handle Vars.Duplicate => raise Pattern
         in
           if Metas.member pvars X then
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
           else
             List.foldl (fn (tm, rho) => proj (pvars, rho) (syms, vars) tm) rho tms
         end
    end
  and projb (pvars, rho) (syms, vars) ((us, xs) \ tm) =
    let
      val syms' = Syms.union syms @@ Syms.fromList us
      val vars' = Vars.union vars @@ Vars.fromList xs
    in
      proj (pvars, rho) (syms', vars') tm
    end

  fun flexRigid (pvars, rho) (X, tau, rs, tms, tm) =
    if occursInTerm rho (X, tm) then
      raise Occurs
    else
      let
        val us = paramsToSymbols rs
        val xs = termsToVariables tms
        val vl = ((List.map #2 rs, List.map sort tms), tau)
        val rho' = Metavar.Ctx.insert rho X @@ checkb ((us, xs) \ tm, vl)
        val syms = Syms.fromListDistinct us handle Syms.Duplicate => raise Pattern
        val vars = Vars.fromListDistinct xs handle Vars.Duplicate => raise Pattern
      in
        proj (pvars, rho') (syms, vars) tm
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
          val rs' = List.mapPartial (fn ((r1, sigma1), (r2, sigma2)) => if O.P.eq Sym.eq (r1, r2) andalso O.Ar.Vl.PS.eq (sigma1, sigma2) then SOME (r1, sigma1) else NONE) @@ ListPair.zipEq (rs1, rs2)
          val tms' = List.mapPartial (fn (tm1, tm2) => if Tm.eq (tm1, tm2) then SOME tm1 else NONE) @@ ListPair.zipEq (tms1, tms2)
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

  exception VariableMismatch
  exception OperatorMismatch
  exception MetavariableMismatch
  exception StructuralMismatch

  fun unifyTerm (pvars, rho) (tm1, tm2) =
    let
      val tau = sort tm1
      val _ = if O.Ar.Vl.S.eq (tau, sort tm2) then () else raise Sort

      val tm1' = shallowSubstMetaenv rho tm1
      val tm2' = shallowSubstMetaenv rho tm2
    in
      unifyView (pvars, rho) tau (out tm1', out tm2')
      handle exn as Unify _ => raise exn
           | exn => raise Unify (tm1', tm2')
    end

  and unifyView (pvars, rho) tau = 
    fn (`x1, `x2) =>
        if Var.eq (x1, x2) then rho else raise VariableMismatch
      | (theta1 $ bs1, theta2 $ bs2) => 
        if O.eq Sym.eq (theta1, theta2) then 
          unifyBinders (pvars, rho) (bs1, bs2)
        else
          raise OperatorMismatch
      | (view1 as X1 $# (rs1, tms1), view2 as X2 $# (rs2, tms2)) =>
        (case (Metas.member pvars X1, Metas.member pvars X2) of 
            (true, true) =>
            if Metavar.eq (X1, X2) then 
              flexFlex1 rho (X1, tau, rs1, rs2, tms1, tms2)
            else
              flexFlex2 rho (X1, X2, tau, rs1, rs2, tms1, tms2)
          | (false, false) =>
            if Metavar.eq (X1, X2) then 
              unifyTerms (pvars, rho) (tms1, tms2)
            else
              raise MetavariableMismatch
          | (true, false) => flexRigid (pvars, rho) (X1, tau, rs1, tms1, check (view2, tau))
          | (false, true) => flexRigid (pvars, rho) (X2, tau, rs2, tms2, check (view1, tau)))
       | (X1 $# (rs1, tms1), view) => 
         if Metas.member pvars X1 then
           flexRigid (pvars, rho) (X1, tau, rs1, tms1, check (view, tau))
         else
           raise StructuralMismatch
       | (view, X2 $# (rs2, tms2)) =>
         if Metas.member pvars X2 then 
           flexRigid (pvars, rho) (X2, tau, rs2, tms2, check (view, tau))
         else
           raise StructuralMismatch
       | _ => raise StructuralMismatch

  and unifyBinder (pvars, rho) ((us1, xs1) \ tm1, (us2, xs2) \ tm2) =
    let
      val sren = ListPair.foldl (fn (u2, u1, ren) => Sym.Ctx.insert ren u2 @@ O.P.ret u1) Sym.Ctx.empty (us2, us1)
      val vren = ListPair.foldl (fn (x2, x1, ren) => Var.Ctx.insert ren x2 x1) Var.Ctx.empty (xs2, xs1)
      val tm2' = substSymenv sren @@ renameVars vren tm2
    in
      unifyTerm (pvars, rho) (tm1, tm2')
    end

  and unifyBinders (pvars, rho) = 
    ListPair.foldlEq
      (fn (b1, b2, rho) => unifyBinder (pvars, rho) (b1, b2))
      rho

  and unifyTerms (pvars, rho) = 
    ListPair.foldlEq
      (fn (tm1, tm2, rho) => unifyTerm (pvars, rho) (tm1, tm2))
      rho

  fun unify pvars = unifyTerm (pvars, Metavar.Ctx.empty)
end