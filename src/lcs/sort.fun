functor LcsSort
  (structure AtomicSort : ABT_SORT
   val opidSort : AtomicSort.t option) : LCS_SORT =
struct
  structure AtomicSort = AtomicSort
  type atomic = AtomicSort.t

  datatype t =
     VAL of atomic
   | CONT of atomic * atomic
   | EXP of atomic

  val eq =
    fn (VAL sigma1, VAL sigma2) => AtomicSort.eq (sigma1, sigma2)
     | (CONT (sigma1, tau1) , CONT (sigma2, tau2)) => AtomicSort.eq (sigma1, sigma2) andalso AtomicSort.eq (tau1, tau2)
     | (EXP sigma1, EXP sigma2) => AtomicSort.eq (sigma1, sigma2)
     | _ => false

  val toString =
    fn VAL sigma => AtomicSort.toString sigma
     | CONT (sigma, tau) => "[" ^ AtomicSort.toString sigma ^ " > " ^ AtomicSort.toString tau ^ "]"
     | EXP sigma => "{" ^ AtomicSort.toString sigma ^ "}"

  val opidSort = opidSort
end
