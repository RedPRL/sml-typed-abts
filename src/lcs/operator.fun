functor LcsOperator (L : LCS_LANGUAGE) : LCS_OPERATOR =
struct
  structure L = L
  open L

  structure S = LcsSort (structure AtomicSort = V.Ar.Vl.S val opidSort = opidSort)
  type sort = S.t
  type valence = (sort list * sort list) * sort
  type arity = valence list * sort

  datatype 'i operator =
     V of 'i V.t
   | K of 'i K.t
   | D of 'i D.t
   | RET of S.atomic
   | CUT of (S.atomic list * S.atomic) * S.atomic
   | ESUBST of ('i * S.atomic) list * S.atomic list * S.atomic
   | CUSTOM of 'i * ('i * S.atomic) list * L.V.Ar.t

  structure V = V and K = K
  structure Ar = ListAbtArity (S)

  type 'i t = 'i operator
  type sort = S.t

  fun mapValence f ((sigmas, taus), tau) =
    ((List.map f sigmas, List.map f taus), f tau)

  val arity =
    fn V theta =>
         let
           val (vls, sigma) = V.arity theta
         in
           (List.map (mapValence S.EXP) vls, S.VAL sigma)
         end
     | K theta =>
         let
           val sigma = input theta
           val (vls, tau) = K.arity theta
         in
           (List.map (mapValence S.EXP) vls, S.CONT (sigma, tau))
         end
     | D theta =>
         let
           val (vls, sigma) = D.arity theta
         in
           (List.map (mapValence S.EXP) vls, S.EXP sigma)
         end
     | RET sigma => ([(([],[]), S.VAL sigma)], S.EXP sigma)
     | CUT ((sigmas, sigma), tau) =>
         ([(([],[]), S.CONT ((sigmas, sigma), tau)),
           ((List.map S.EXP sigmas, []), S.EXP sigma)],
          S.EXP tau)
     | ESUBST (us, taus, tau) =>
        let
          val vl = ((List.map #2 us, taus), tau)
          val args = List.map (fn tau => (([],[]), S.EXP tau)) taus
        in
          ([mapValence S.EXP vl] @ args, S.EXP tau)
        end
     | CUSTOM (_, _, (vls, sigma)) =>
         (List.map (mapValence S.EXP) vls, S.EXP sigma)

  val support =
    fn V theta => List.map (fn (u, sigma) => (u, S.EXP sigma)) (V.support theta)
     | K theta => List.map (fn (u, sigma) => (u, S.EXP sigma)) (K.support theta)
     | D theta => List.map (fn (u, sigma) => (u, S.EXP sigma)) (D.support theta)
     | CUSTOM (opid, params, _) =>
         (case L.opidSort of
             NONE => raise Fail "You forgot to implement opidSort"
           | SOME sigma =>
               let
                 val supp = (opid, sigma) :: params
               in
                 List.map (fn (u, tau) => (u, S.EXP tau)) supp
               end)
     | _ => []

  fun eq f =
    fn (V theta1, V theta2) => V.eq f (theta1, theta2)
     | (K theta1, K theta2) => K.eq f (theta1, theta2)
     | (D theta1, D theta2) => D.eq f (theta1, theta2)
     | (CUT ((sigmas1, sigma1), tau1), CUT ((sigmas2, sigma2), tau2)) =>
         ListPair.allEq S.AtomicSort.eq (sigmas1, sigmas2)
           andalso S.AtomicSort.eq (sigma1, sigma2)
           andalso S.AtomicSort.eq (tau1, tau2)
     | (RET sigma1, RET sigma2) =>
        S.AtomicSort.eq (sigma1, sigma2)
     | (CUSTOM (opid1, supp1, arity1), CUSTOM (opid2, supp2, arity2)) =>
        f (opid1, opid2)
          andalso ListPair.allEq (fn ((u, sigma), (v, tau)) => f (u, v) andalso S.AtomicSort.eq (sigma, tau)) (supp1, supp2)
          andalso V.Ar.eq (arity1, arity2)
     | (ESUBST (us1, taus1, tau1), ESUBST (us2, taus2, tau2)) =>
         let
           val vl1 = ((List.map #2 us1, taus1), tau1)
           val vl2 = ((List.map #2 us2, taus2), tau2)
         in
           ListPair.allEq (fn ((u, _), (v, _)) => f (u, v)) (us1, us2)
             andalso V.Ar.Vl.eq (vl1, vl2)
         end
     | _ => false

  fun toString f =
    fn V theta => V.toString f theta
     | K theta => K.toString f theta
     | D theta => D.toString f theta
     | RET _ => "ret"
     | CUT _ => "cut"
     | ESUBST _ => "subst"
     | CUSTOM (opid, supp : ('i * S.atomic) list, _) =>
         let
           fun params [] = ""
             | params xs = "[" ^ ListSpine.pretty (fn (u, _) => f u) "," xs ^ "]"
         in
           f opid ^ params supp
         end

  fun map f =
    fn V theta => V (V.map f theta)
     | K theta => K (K.map f theta)
     | D theta => D (D.map f theta)
     | RET sigma => RET sigma
     | CUT (sigma, tau) => CUT (sigma, tau)
     | ESUBST (us, taus, tau) => ESUBST (List.map (fn (u, sigma) => (f u, sigma)) us, taus, tau)
     | CUSTOM (opid, supp, arity) => CUSTOM (f opid, List.map (fn (u, tau) => (f u, tau)) supp, arity)
end
