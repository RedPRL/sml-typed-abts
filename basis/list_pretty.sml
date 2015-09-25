structure ListPretty : LIST_PRETTY =
struct
  fun pretty f (sep, xs) =
    let
      fun go [] = ""
        | go (x :: []) = f x
        | go (x :: xs) = f x ^ sep ^ go xs
    in
      go xs
    end
end

