module Verified

import Eff

interface Functor f => VerifiedFunctor (0 f : Type -> Type) where
  functorIdentity : (g : a -> a) -> ((v : a) -> g v = v) -> (x : f a) -> map g x = x
  functorComposition : (x : f a) ->
                       (g1 : a -> b) -> (g2 : b -> c) ->
                       map (g2 . g1) x = (map g2 . map g1) x


interface (Applicative f, VerifiedFunctor f) => VerifiedApplicative (f : Type -> Type) where
  applicativeMap : (x : f a) -> (g : a -> b) ->
                   map g x = pure g <*> x
  applicativeIdentity : (x : f a) -> pure Basics.id <*> x = x
  applicativeComposition : (x : f a) -> (g1 : f (a -> b)) -> (g2 : f (b -> c)) ->
                           ((pure (.) <*> g2) <*> g1) <*> x = g2 <*> (g1 <*> x)
  applicativeHomomorphism : (x : a) -> (g : a -> b) ->
                            (<*>) {f} (pure g) (pure x) = pure {f} (g x)
  applicativeInterchange : (x : a) -> (g : f (a -> b)) ->
                           g <*> pure x = pure (\g' : (a -> b) => g' x) <*> g

interface (Monad m, VerifiedApplicative m) => VerifiedMonad (m : Type -> Type) where
  monadApplicative : (mf : m (a -> b)) -> (mx : m a) ->
                     mf <*> mx = mf >>= \f =>
                                 mx >>= \x =>
                                        pure (f x)
  monadLeftIdentity : (x : a) -> (f : a -> m b) -> pure x >>= f = f x
  monadRightIdentity : (mx : m a) -> mx >>= Prelude.Interfaces.pure = mx
  monadAssociativity : (mx : m a) -> (f : a -> m b) -> (g : b -> m c) ->
                       (mx >>= f) >>= g = mx >>= (\x => f x >>= g)

VerifiedFunctor f => VerifiedFunctor (Free f) where
  -- functorIdentity : VerifiedFunctor f =>
  -- (g : a -> a)
  -- -> ((v : a) -> g v = v)
  -- -> (x : Free f a)
  -- -> map g x = x
  functorIdentity g p (Pure x) = cong Pure (p x)
  functorIdentity g p (Impure fx) =
    let func = functorIdentity {f} g p
    in cong Impure ?h

  functorComposition x g1 g2 = ?h1
