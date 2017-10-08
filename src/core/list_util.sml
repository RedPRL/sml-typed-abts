structure ListUtil :> LIST_UTIL = 
struct
  fun isEmpty [] = true
    | isEmpty _ = false

  fun joinWith f sep =
    let
      fun go [] = ""
        | go (x :: []) = f x
        | go (x :: xs) = f x ^ sep ^ go xs
    in
      go
    end
end