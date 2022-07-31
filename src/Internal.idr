module Internal

import public FTCQueue
import public Union

mutual
  ||| The Eff monad provides the implementation of a computation that performs an arbitrary
  ||| set of algebraic effects. In `Eff effs a`, `effs` is a type-level list that contains
  ||| all the effects that the computation may perform. Furthermore `a` is the response type
  ||| which is returned after running the effects.
  public export
  data Eff : (effs : List (Type -> Type)) -> (a : Type) -> Type where
    Pure : a -> Eff effs a
    Impure : Union effs x -> Arrs effs x a -> Eff effs a

  public export
  ||| Type synonym representing the composition of functions (continuation segments);
  ||| a -> Eff r t1, t1 -> Eff r t2, ..., tn -> Eff r b.
  Arrs : (r : List (Type -> Type)) -> (a, b : Type) -> Type
  Arrs r a b = FTCQueue (Eff r) a b

public export
||| Type synonym for functions that map `a` to `b`, but also do effects denoted by `r`.
Arr : (r : List (Type -> Type)) -> (a, b : Type) -> Type
Arr r a b = a -> Eff r b

-- TODO: Is `qApp` not total?
||| Function application in the context of an array of effects, `Arrs effs b w`.
public export
qApp : Arrs effs b w -> b -> Eff effs w
qApp q' x = case tviewl q' of
  TOne k => k x
  k :| t => case k x of
    Pure y => qApp t y
    Impure u q => Impure u (q >< t)

||| Composition of effectful arrows ('Arrs'). Allows for the caller to change the
||| effect environment, as well.
public export
qComp : Arrs effs a b -> (Eff effs b -> Eff effs' c) -> Arr effs' a c
qComp g h a = h $ qApp g a

public export
implementation Functor (Eff effs) where
  --map : (a -> b) -> Eff effs a -> Eff effs b
  map f (Pure a) = Pure (f a)
  map f (Impure u g) = Impure u (g |> (Pure . f))

public export
implementation Applicative (Eff effs) where
  -- pure : a -> Eff effs a
  pure = Pure
  -- (<*>) : Eff effs (a -> b) -> Eff effs a -> Eff effs b
  Pure f <*> Pure a = Pure (f a)
  Pure f <*> Impure u q = Impure u (q |> (Pure . f))
  Impure u q <*> m = Impure u (q |> (<$> m))

public export
implementation Monad (Eff effs) where
  -- (>>=) : Eff effs a -> (a -> Eff effs b) -> Eff effs b
  Pure a >>= k = k a
  Impure u q >>= k = Impure u (q |> k)

public export
||| Given a request, either handle it or relay it.
handleRelay
  : (a -> Eff effs b)
  -- ^ Handle a pure value.
  -> (forall v. eff v -> Arr effs v b -> Eff effs b)
  -- ^ Handle a request for effect of type `eff : Type -> Type`.
  -> Eff (eff :: effs) a
  -> Eff effs b
handleRelay ret _ (Pure x) = ret x
handleRelay ret impure (Impure u q) =
  let k = qComp q (handleRelay ret impure) in
  case decomp u of
    Right x => impure x k
    Left u => Impure u (tsingleton k)

public export
||| Parameterized 'handleRelay'. Allows sending along some state of type
||| `s : Type` to be handled for the target effect, or relayed to a handler that
||| can handle the target effect.
handleRelayS
  : s
  -> (s -> a -> Eff effs b)
  -- ^ Handle a pure value.
  -> (forall v. s -> eff v -> (s -> Arr effs v b) -> Eff effs b)
  -- ^ Handle a request for effect of type `eff : Type -> Type`.
  -> Eff (eff :: effs) a
  -> Eff effs b
  -- ^ Result with effects of type `eff : Type -> Type` handled.
handleRelayS s' ret h = loop s'
  where
    loop : s -> Eff (eff :: effs) a -> Eff effs b
    loop s (Pure x)  = ret s x
    loop s (Impure u' q) =
      let k = \s'' => loop s'' . qApp q in
      case decomp u' of
        Right x => h s x k
        Left  u => Impure u (tsingleton (k s))

public export
||| Interpret an effect by transforming it into another effect on top of the
||| stack.
replaceRelay
  : (a -> Eff (v :: effs) w)
  -> (forall x. t x -> Arr (v :: effs) x w -> Eff (v :: effs) w)
  -> Eff (t :: effs) a
  -> Eff (v :: effs) w
replaceRelay pure' bind = loop
  where
    loop : Eff (t :: effs) a -> Eff (v :: effs) w
    loop (Pure x) = pure' x
    loop (Impure u' q) =
      let k = qComp q loop in
      case decomp u' of
        Right x => bind x k
        Left  u => Impure (weaken u) (tsingleton k)

public export
partial
||| Runs a pure Eff computation, since an Eff computation that performs no effects
||| (i.e. has no effects in its type-level list) is guaranteed to be pure. This
||| is usually used as the final step of running an effectful computation, after all
||| other effects have been discharged using effect handlers.
run : Eff [] a -> a
run (Pure x) = x

public export
runM : Monad m => Eff [m] a -> m a
runM (Pure x) = pure x
runM (Impure u q) = case extract u of
  mb => mb >>= runM . qApp q
