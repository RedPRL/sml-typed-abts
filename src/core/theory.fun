functor FreshSymbols (S : ABT_SYMBOL) =
struct
  fun freshSyms ss =
    let
      fun go ctx [] = []
        | go ctx (s :: ss) =
            let
              val u = S.fresh ctx "?"
            in
              (u, s) :: go (S.Ctx.insert ctx u ()) ss
            end
    in
      go S.Ctx.empty ss
    end
end

functor AbtLawvereTheory (Abt : ABT where type 'a O.Ar.Vl.Sp.t = 'a list) :
sig
  include LAWVERE_THEORY

  val toList : term -> Abt.abs list
end =
struct
  type sort = Abt.valence
  type var = Abt.metavariable
  type ctx = Abt.metactx

  structure Env = Abt.Metavar.Ctx

  datatype term = ## of Abt.metaenv * Abt.metaenv Env.dict
  infix ##

  val empty =
    Env.empty ## Env.empty

  exception Union
  fun union (xs, ys) =
    Env.union xs ys (fn _ => raise Union)

  fun fork (x, e0 ## e1) (y, f0 ## f1) =
    let
      val ef0 = union (e0, f0)
      val ef1 = union (e1, f1)
      val ef1' = Env.insert ef1 x e0
      val ef1'' = Env.insert ef1' y f0
    in
      ef0 ## ef1''
    end

  fun snoc (e0 ## e1) (y, abs) =
    let
      val e0' = Env.insert e0 y abs
      val e1' = Env.insert e1 y (Env.insert Env.empty y abs)
    in
      e0' ## e1'
    end

  local
    structure FreshSyms = FreshSymbols (Abt.Sym) and FreshVars = FreshSymbols (Abt.Var)

    fun metavar (x, vl) =
      let
        open Abt infix \ $#
        val ((sigmas, taus), tau) = vl
        val syms = FreshSyms.freshSyms sigmas
        val params = List.map (fn (a, sigma) => (O.P.ret a, sigma)) syms
        val vars = FreshVars.freshSyms taus
        val varTerms = List.map (fn (x,tau) => check (`x, tau)) vars
        val tm = check (x $# (params, varTerms), tau)
      in
        checkb ((List.map #1 syms, List.map #1 vars) \ tm, vl)
      end
  in
    fun proj psi =
      Env.foldl (fn (x, vl, r) => snoc r (x, metavar (x, vl))) empty psi
  end

  local
    val subst0 = Abt.mapAbs o Abt.substMetaenv
    val subst1 = Env.map o subst0
  in
    fun subst (e0 ## e1) (f0 ## f1) =
      Env.map (subst0 e0) f0
        ## Env.map (subst1 e0) f1
  end

  fun ctx (e0 ## _) =
    Env.map Abt.valence e0

  fun toList (e0 ## _) =
    List.map #2 (Env.toList e0)

  fun lookup x (e as e0 ## e1) =
    let
      val rho = Env.lookup e1 x
      val psi = Env.map Abt.valence rho
    in
      subst e (proj psi)
    end
end
