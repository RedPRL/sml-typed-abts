structure AbtIdParam =
struct
  type 'i t = 'i
  fun pure x = x
  fun bind f x = f x

  fun extract x = SOME x
  fun eq f = f
  fun toString f = f
end

structure AbtCubicalParam =
struct
  datatype 'i t =
     NAME of 'i
   | DIM0
   | DIM1

  val pure = NAME

  fun bind f =
    fn NAME u => f u
     | DIM0 => DIM0
     | DIM1 => DIM1

  val extract =
    fn NAME u => SOME u
     | _ => NONE

  fun eq f =
    fn (NAME u, NAME v) => f (u, v)
     | (DIM0, DIM0) => true
     | (DIM1, DIM1) => true
     | _ => false

  fun toString f =
    fn NAME u => f u
     | DIM0 => "dim0"
     | DIM1 => "dim1"
end
