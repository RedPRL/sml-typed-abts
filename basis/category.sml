structure FunctionCategory =
struct
  type ('a, 'b) hom = 'a -> 'b
  fun id x = x
  val comp = op o
end
