signature VALENCE =
sig
  type sort
  type valence = sort list * sort

  include
    sig
      include SHOW
      include EQ
    end
    where type t = valence
end

