signature VALENCE =
sig
  type sort
  structure Spine : SPINE
  type valence = sort Spine.t * sort

  include
    sig
      include SHOW
      include EQ
    end
    where type t = valence
end

