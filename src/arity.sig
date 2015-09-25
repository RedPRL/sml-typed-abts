signature ARITY =
sig
  structure Sort : SORT
  structure Valence : VALENCE
  sharing type Valence.sort = Sort.sort

  type arity = Valence.t list * Sort.t

  include
    sig
      include SHOW
      include EQ
    end
    where type t  = arity
end


