functor LcsSort (AtomicSort : SORT) : LCS_SORT =
struct
  structure AtomicSort = AtomicSort
  type atomic = AtomicSort.t

  datatype t =
     VAL of atomic
   | CONT of atomic * atomic
   | CMD of atomic

  val eq =
    fn (VAL sigma1, VAL sigma2) => AtomicSort.eq (sigma1, sigma2)
     | (CONT (sigma1, tau1) , CONT (sigma2, tau2)) => AtomicSort.eq (sigma1, sigma2) andalso AtomicSort.eq (tau1, tau2)
     | (CMD sigma1, CMD sigma2) => AtomicSort.eq (sigma1, sigma2)
     | _ => false

  val toString =
    fn VAL sigma => AtomicSort.toString sigma
     | CONT (sigma, tau) => "[" ^ AtomicSort.toString sigma ^ " > " ^ AtomicSort.toString tau ^ "]"
     | CMD sigma => "{" ^ AtomicSort.toString sigma ^ "}"
end
