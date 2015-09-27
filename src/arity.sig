signature ARITY =
sig
  structure Sort : SORT
  structure Valence : VALENCE
  sharing type Valence.sort = Sort.sort

  structure Spine : SPINE

  type arity = Valence.t Spine.t * Sort.t

  include
    sig
      include SHOW
      include EQ
    end
    where type t  = arity
end


