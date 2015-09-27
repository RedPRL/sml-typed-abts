signature CATEGORY =
sig
  type ('a, 'b) hom
  val id : ('a, 'a) hom
  val comp : ('b, 'c) hom * ('a, 'b) hom -> ('a, 'c) hom
end
