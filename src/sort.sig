signature SORT =
sig
  type sort
  include
    sig
      include EQ
      include SHOW
    end
    where type t = sort
end

