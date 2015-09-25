signature VARIABLE =
sig
  type variable
  val named : string -> variable

  include
    sig
      include EQ
      include SHOW
    end
    where type t = variable

  val compare : variable * variable -> order
  val clone : variable -> variable
end

