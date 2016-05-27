functor LcsOperator
  (structure Sort : LCS_SORT
   structure Val : OPERATOR where type 'a Arity.Valence.Spine.t = 'a list
   structure Cont : CONT_OPERATOR where type 'a Arity.Valence.Spine.t = 'a list
   sharing type Val.Arity.Valence.Sort.t = Sort.AtomicSort.t
   sharing type Cont.Arity.Valence.Sort.t = Sort.AtomicSort.t) : LCS_OPERATOR =
struct
  type sort = Sort.t
  type valence = (sort list * sort list) * sort
  type arity = valence list * sort

  datatype 'i operator =
     V of 'i Val.t
   | K of 'i Cont.t
   | RET of Sort.atomic
   | CUT of Sort.atomic * Sort.atomic


  structure Sort = Sort and Val = Val and Cont = Cont
  structure Arity = ListArity (Sort)

  type 'i t = 'i operator
  type sort = Sort.t

  fun mapValence f ((sigmas, taus), tau) =
    ((List.map f sigmas, List.map f taus), f tau)

  val arity =
    fn V theta =>
         let
           val (vls, sigma) = Val.arity theta
         in
           (List.map (mapValence Sort.EXP) vls, Sort.VAL sigma)
         end
     | K theta =>
         let
           val sigma = Cont.input theta
           val (vls, tau) = Cont.arity theta
         in
           (List.map (mapValence Sort.EXP) vls, Sort.CONT (sigma, tau))
         end
     | RET sigma => ([(([],[]), Sort.VAL sigma)], Sort.EXP sigma)
     | CUT (sigma, tau) =>
       ([(([],[]), Sort.CONT (sigma, tau)),
         (([],[]), Sort.EXP sigma)],
        Sort.EXP tau)

  val support =
    fn V theta => List.map (fn (u, sigma) => (u, Sort.VAL sigma)) (Val.support theta)
     | K theta => List.map (fn (u, sigma) => (u, Sort.VAL sigma)) (Cont.support theta)
     | _ => []

  fun eq f =
    fn (V theta1, V theta2) => Val.eq f (theta1, theta2)
     | (K theta1, K theta2) => Cont.eq f (theta1, theta2)
     | (CUT (sigma1, tau1), CUT (sigma2, tau2)) =>
         Sort.AtomicSort.eq (sigma1, sigma2)
           andalso Sort.AtomicSort.eq (tau1, tau2)
     | (RET sigma1, RET sigma2) =>
        Sort.AtomicSort.eq (sigma1, sigma2)
     | _ => false

  fun toString f =
    fn V theta => Val.toString f theta
     | K theta => Cont.toString f theta
     | RET _ => "ret"
     | CUT _ => "cut"

  fun map f =
    fn V theta => V (Val.map f theta)
     | K theta => K (Cont.map f theta)
     | RET sigma => RET sigma
     | CUT (sigma, tau) => CUT (sigma, tau)
end
