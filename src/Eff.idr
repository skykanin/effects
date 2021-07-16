module Eff

public export
data Free : (f : Type -> Type) -> (a : Type) -> Type where
  Pure : a -> Free f a
  Impure : f (Free f a) -> Free f a

export
Functor f => Functor (Free f) where
  map f (Pure a) = Pure (f a)
  map f (Impure fa) = Impure (map f <$> fa)

export
Functor f => Applicative (Free f) where
  pure = Pure

  f <*> Pure a = ($ a) <$> f
  f <*> Impure fa = Impure ((f <*>) <$> fa)

export
Functor f => Monad (Free f) where
  Pure a >>= f = f a
  Impure fa >>= f = Impure ((>>= f) <$> fa)

infixr 0 ~>
(~>) : (Type -> Type) -> (Type -> Type) -> Type
(~>) f g = {a : Type} -> f a -> g a

{-
freeM : (Functor f, Functor g) => ({a : Type} -> f a -> g a)
                               -> ({b : Type} -> Free f b -> Free g b)
freeM _ (Pure x) = Pure x
freeM phi (Impure fx) = Impure $ phi ?h
-}
