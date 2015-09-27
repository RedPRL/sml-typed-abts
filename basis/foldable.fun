functor CategoryFoldMap (structure C : CATEGORY and F : FOLDABLE) =
struct
  fun foldMap (f : 'a -> ('b, 'b) C.hom) =
    F.foldr (fn (a, phi) => C.comp (f a, phi)) C.id
end
