signature VARIABLE =
sig
  type variable
  val named : string -> variable

  structure Show : SHOW where type t = variable
  structure DebugShow : SHOW where type t = variable

  include
    sig
      include EQ
    end
    where type t = variable

  val compare : variable * variable -> order
  val clone : variable -> variable
end

