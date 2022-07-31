module Util

%default total

infixr 0 ~>
||| A natural transformation from `f` to `g`.
public export
0 (~>) : (f : k -> Type) -> (g : k -> Type) -> Type
f ~> g = {0 x : k} -> f x -> g x
