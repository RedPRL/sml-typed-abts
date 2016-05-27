functor LcsOperator (L : LCS_LANGUAGE) : LCS_OPERATOR =
struct
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

  structure Sort = Sort and V = V and K = K
  structure Arity = ListArity (Sort)

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

  val support =
    fn V theta => List.map (fn (u, sigma) => (u, Sort.VAL sigma)) (V.support theta)
     | K theta => List.map (fn (u, sigma) => (u, Sort.VAL sigma)) (K.support theta)
     | _ => []

  fun eq f =
    fn (V theta1, V theta2) => V.eq f (theta1, theta2)
     | (K theta1, K theta2) => K.eq f (theta1, theta2)
     | (CUT (sigma1, tau1), CUT (sigma2, tau2)) =>
         Sort.AtomicSort.eq (sigma1, sigma2)
           andalso Sort.AtomicSort.eq (tau1, tau2)
     | (RET sigma1, RET sigma2) =>
        Sort.AtomicSort.eq (sigma1, sigma2)
     | _ => false

  fun toString f =
    fn V theta => V.toString f theta
     | K theta => K.toString f theta
     | RET _ => "ret"
     | CUT _ => "cut"

  fun map f =
    fn V theta => V (V.map f theta)
     | K theta => K (K.map f theta)
     | RET sigma => RET sigma
     | CUT (sigma, tau) => CUT (sigma, tau)
end
