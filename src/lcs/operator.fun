functor LcsOperator (L : LCS_LANGUAGE) : LCS_OPERATOR =
struct
  structure L = L
  open L

  structure Sort = LcsSort (structure AtomicSort = V.Arity.Valence.Sort val opidSort = opidSort)
  type sort = Sort.t
  type valence = (sort list * sort list) * sort
  type arity = valence list * sort

  datatype 'i operator =
     V of 'i V.t
   | K of 'i K.t
   | RET of Sort.atomic
   | CUT of Sort.atomic * Sort.atomic
   | CUSTOM of 'i * ('i * Sort.atomic) list * L.V.Arity.t

  structure Sort = Sort and V = V and K = K
  structure Arity = ListAbtArity (Sort)

  type 'i t = 'i operator
  type sort = Sort.t

  fun mapValence f ((sigmas, taus), tau) =
    ((List.map f sigmas, List.map f taus), f tau)

  val arity =
    fn V theta =>
         let
           val (vls, sigma) = V.arity theta
         in
           (List.map (mapValence Sort.EXP) vls, Sort.VAL sigma)
         end
     | K theta =>
         let
           val sigma = input theta
           val (vls, tau) = K.arity theta
         in
           (List.map (mapValence Sort.EXP) vls, Sort.CONT (sigma, tau))
         end
     | RET sigma => ([(([],[]), Sort.VAL sigma)], Sort.EXP sigma)
     | CUT (sigma, tau) =>
         ([(([],[]), Sort.CONT (sigma, tau)),
           (([],[]), Sort.EXP sigma)],
          Sort.EXP tau)
     | CUSTOM (_, _, (vls, sigma)) =>
         (List.map (mapValence Sort.EXP) vls, Sort.EXP sigma)

  val support =
    fn V theta => List.map (fn (u, sigma) => (u, Sort.VAL sigma)) (V.support theta)
     | K theta => List.map (fn (u, sigma) => (u, Sort.VAL sigma)) (K.support theta)
     | CUSTOM (opid, params, _) =>
         (case L.opidSort of
             NONE => raise Fail "You forgot to implement opidSort"
           | SOME sigma =>
               let
                 val supp = (opid, sigma) :: params
               in
                 List.map (fn (u, tau) => (u, Sort.EXP tau)) supp
               end)
     | _ => []

  fun eq f =
    fn (V theta1, V theta2) => V.eq f (theta1, theta2)
     | (K theta1, K theta2) => K.eq f (theta1, theta2)
     | (CUT (sigma1, tau1), CUT (sigma2, tau2)) =>
         Sort.AtomicSort.eq (sigma1, sigma2)
           andalso Sort.AtomicSort.eq (tau1, tau2)
     | (RET sigma1, RET sigma2) =>
        Sort.AtomicSort.eq (sigma1, sigma2)
     | (CUSTOM (opid1, supp1, arity1), CUSTOM (opid2, supp2, arity2)) =>
        f (opid1, opid2)
          andalso ListPair.allEq (fn ((u, sigma), (v, tau)) => f (u, v) andalso Sort.AtomicSort.eq (sigma, tau)) (supp1, supp2)
          andalso V.Arity.eq (arity1, arity2)
     | _ => false

  fun toString f =
    fn V theta => V.toString f theta
     | K theta => K.toString f theta
     | RET _ => "ret"
     | CUT _ => "cut"
     | CUSTOM (opid, supp : ('i * Sort.atomic) list, _) =>
         let
           fun params [] = ""
             | params xs = "[" ^ ListSpine.pretty (fn (u, _) => f u) "," xs ^ "]"
         in
           f opid ^ params supp
         end

  fun map f =
    fn V theta => V (V.map f theta)
     | K theta => K (K.map f theta)
     | RET sigma => RET sigma
     | CUT (sigma, tau) => CUT (sigma, tau)
     | CUSTOM (opid, supp, arity) => CUSTOM (f opid, List.map (fn (u, tau) => (f u, tau)) supp, arity)
end
