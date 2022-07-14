||| An implementation of an extensible effect system based on freer monads
||| which leverages dependent types to enforce invariants in a type safe manner.
||| Sources:
|||  - https://okmij.org/ftp/Haskell/extensible/more.pdf
|||  - https://hackage.haskell.org/package/freer-simple-1.2.1.2
module Eff

%default total

||| A proof that the type constructor `f` is a member of the
||| type constructor list `fs`.
data Member : (f : Type -> Type) -> (fs : List (Type -> Type)) -> Type where
  Here : Member f (f :: fs)
  There : Member f fs -> Member f (g :: fs)

||| A shorthand constraint that represents a combination of multiple 'Member'
||| constraints.
Members : List (Type -> Type) -> List (Type -> Type) -> Type
Members [] effs = ()
Members (x :: xs) effs = Member x effs => Members xs effs

||| Like `Member` except `f` must now be the *last* member of `fs`.
data LastMember : (f : Type -> Type) -> (fs : List (Type -> Type)) -> Type where
  End : LastMember f [f]
  Further : LastMember f fs -> LastMember f (g :: fs)

export %hint
||| If you have a proof `LastMember eff effs` you also have a proof
||| `Member eff effs`. This defines a hierarchy of proofs which can
||| be used by the compiler when proof searching.
lastMemberToMember : (m : LastMember f fs) => Member f fs
lastMemberToMember {m = End} = Here
lastMemberToMember {m = Further x} = There lastMemberToMember

||| Open union of effects carrying a proof that a given `eff` exists
||| in the list of effects `effs`.
data Union : (effs : List (Type -> Type)) -> (x : Type) -> Type where
  Element : Member eff effs -> (v : eff x) -> Union effs x

inj : (ix : Member eff effs) => (v : eff a) -> Union effs a
inj v = Element ix v

prj : (ix : Member eff effs) => Union effs a -> Maybe (eff a)
prj {ix = Here} (Element Here v)= Just v
prj {ix = There _} (Element (There x) v)= prj $ Element x v
prj _ = Nothing

decomp : Union (t :: r) a -> Either (Union r a) (t a)
decomp (Element Here v) = Right v
decomp (Element (There x) v) = Left (Element x v)

extract : Union [t] a -> t a
extract (Element Here a) = a

||| Inject whole `Union r` into a weaker `Union (a :: r)` that has one more summand.
weaken : Union r a -> Union (e :: r) a
weaken (Element p v) = Element (There p) v

||| Non-empty tree. Deconstruction operations make it more and more left-leaning.
data FTCQueue : (m : Type -> Type) -> (a, b : Type) -> Type where
  Leaf : (a -> m b) -> FTCQueue m a b
  Node : FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b

||| Build a leaf from a single operation. [O(1)]
tsingleton : (a -> m b) -> FTCQueue m a b
tsingleton = Leaf

infixl 1 |>
||| Append an operation to the right of the tree. [O(1)]
(|>) : FTCQueue m a x -> (x -> m b) -> FTCQueue m a b
t |> r = Node t (Leaf r)

infixr 6 ><
||| Append two trees of operations. [O(1)]
(><) : FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b
t1 >< t2 = Node t1 t2

infixl 4 :|
||| Left view deconstruction data structure.
data ViewL : (m : Type -> Type) -> (a, b : Type) -> Type where
  TOne : (a -> m b) -> ViewL m a b
  (:|) : (a -> m x) -> (FTCQueue m x b) -> ViewL m a b

||| Left view deconstruction. [average O(1)]
tviewl : FTCQueue m a b -> ViewL m a b
tviewl (Leaf r)     = TOne r
tviewl (Node t1 t2) = go t1 t2
  where
    go : FTCQueue m a x -> FTCQueue m x b -> ViewL m a b
    go (Leaf r)       tr = r :| tr
    go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)

mutual
  ||| The Eff monad provides the implementation of a computation that performs an arbitrary
  ||| set of algebraic effects. In `Eff effs a`, `effs` is a type-level list that contains
  ||| all the effects that the computation may perform. Furthermore `a` is the response type
  ||| which is returned after running the effects.
  data Eff : (effs : List (Type -> Type)) -> (a : Type) -> Type where
    Pure : a -> Eff effs a
    Impure : Union effs x -> Arrs effs x a -> Eff effs a

  ||| Type synonym representing the composition of functions (continuation segments);
  ||| a -> Eff r t1, t1 -> Eff r t2, ..., tn -> Eff r b.
  Arrs : (r : List (Type -> Type)) -> (a, b : Type) -> Type
  Arrs r a b = FTCQueue (Eff r) a b

||| Type synonym for functions that map `a` to `b`, but also do effects denoted by `r`.
Arr : (r : List (Type -> Type)) -> (a, b : Type) -> Type
Arr r a b = a -> Eff r b

-- TODO: Is `qApp` not total?
covering
||| Function application in the context of an array of effects, `Arrs effs b w`.
qApp : Arrs effs b w -> b -> Eff effs w
qApp q' x = case tviewl q' of
  TOne k => k x
  k :| t => case k x of
    Pure y => qApp t y
    Impure u q => Impure u (q >< t)

covering
||| Composition of effectful arrows ('Arrs'). Allows for the caller to change the
||| effect environment, as well.
qComp : Arrs effs a b -> (Eff effs b -> Eff effs' c) -> Arr effs' a c
qComp g h a = h $ qApp g a

covering
implementation Functor (Eff effs) where
  --map : (a -> b) -> Eff effs a -> Eff effs b
  map f (Pure a) = Pure (f a)
  map f (Impure u g) = Impure u (g |> (Pure . f))

covering
implementation Applicative (Eff effs) where
  -- pure : a -> Eff effs a
  pure = Pure
  -- (<*>) : Eff effs (a -> b) -> Eff effs a -> Eff effs b
  Pure f <*> Pure a = Pure (f a)
  Pure f <*> Impure u q = Impure u (q |> (Pure . f))
  Impure u q <*> m = Impure u (q |> (<$> m))

covering
implementation Monad (Eff effs) where
  -- (>>=) : Eff effs a -> (a -> Eff effs b) -> Eff effs b
  Pure a >>= k = k a
  Impure u q >>= k = Impure u (q |> k)

covering
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

covering
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

covering
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

infixr 0 ~>
||| A natural transformation from `f` to `g`.
0 (~>) : (f : k -> Type) -> (g : k -> Type) -> Type
f ~> g = {0 x : k} -> f x -> g x

covering
||| The simplest way to produce an effect handler. Given a natural
||| transformation from some effect `eff` to some effectful computation with
||| effects `effs`, produces a natural transformation from `Eff (eff :: effs)`
||| to `'Eff effs`.
interpret : (eff ~> Eff effs) -> (Eff (eff :: effs) ~> Eff effs)
interpret f = handleRelay pure (\e => (f e >>=))

||| "Sends" an effect, which should be a value defined as part of an effect
||| algebra, to an effectful computation. This is used to connect the definition
||| of an effect to the `Eff` monad so that it can be used and handled.
send : Member eff effs => eff a -> Eff effs a
send t = Impure (inj t) (tsingleton Pure)

||| Identical to send, but specialised to the final effect in effs to assist type inference.
sendM : (Monad m, LastMember m effs) => m a -> Eff effs a
sendM = send

covering
||| Like interpret, this function runs an effect without introducing another one.
||| However, this runs the effect in a final monad in effs, intended to be run with `runM`.
interpretM : (Monad m, LastMember m effs) => (eff ~> m) -> Eff (eff :: effs) ~> Eff effs
interpretM f = interpret (sendM . f)

covering
||| Like `interpret`, but instead of removing the interpreted effect `eff1`, reencodes it in
||| some new effect `eff2`.
reinterpret : (eff1 ~> Eff (eff2 :: effs)) -> Eff (eff1 :: effs) ~> Eff (eff2 :: effs)
reinterpret f = replaceRelay pure (\e => (f e >>=))

partial
||| Runs a pure Eff computation, since an Eff computation that performs no effects
||| (i.e. has no effects in its type-level list) is guaranteed to be pure. This
||| is usually used as the final step of running an effectful computation, after all
||| other effects have been discharged using effect handlers.
run : Eff [] a -> a
run (Pure x) = x

covering
runM : Monad m => Eff [m] a -> m a
runM (Pure x) = pure x
runM (Impure u q) = case extract u of
  mb => mb >>= runM . qApp q

---------------------------------- Abort ----------------------------------

||| An effect for aborting the execution.
data Abort a = MkAbort

||| Function for aborting a computation.
abort : Member Abort effs => Eff effs a
abort = send MkAbort

covering
||| Handler for aborting effect. If `abort` is called then the execution
||| is aborted and Nothing is returned.
runAbort : Eff (Abort :: effs) a -> Eff effs (Maybe a)
runAbort = handleRelay (pure . Just) (\MkAbort, _ => pure Nothing)

||| An example abort computation.
abortComp : Member Abort effs => List Int -> Eff effs (List Int)
abortComp = traverse (\x => if isEven x then pure x else abort)
  where
    isEven : Int -> Bool
    isEven n = n `mod` 2 == 0

notAborted : (Eff.run . Eff.runAbort . Eff.abortComp) [0, 2] = Just [0, 2]
notAborted = Refl

aborted : (Eff.run . Eff.runAbort . Eff.abortComp) [0, 1, 2] = Nothing
aborted = Refl

---------------------------------- Error ----------------------------------

||| An effect for aborting execution with an error message.
data Error : (e, r : Type) -> Type where
  ThrowError : e -> Error e r

||| Function for aborting a computation with an error
throwError : Member (Error e) effs => e -> Eff effs a
throwError = send . ThrowError

covering
||| Handler for error effect. If `throwError` is called then the execution
||| is aborted and the error type is returned.
runError : Eff ((Error e) :: effs) a -> Eff effs (Either e a)
runError = handleRelay (pure . Right) (\(ThrowError e), _ => pure $ Left e)

||| An example error computation.
errorComp : Member (Error String) effs => Int -> Eff effs Int
errorComp n =
  if n /= 0
  then pure $ 10 `div` n
  else throwError "Cannot divide by zero"

-- Need to help idris with type inference here
noError : (Eff.run . Eff.runError . Eff.errorComp) 5 = the (Either String Int) (Right 2)
noError = Refl

erronious : (Eff.run . Eff.runError . Eff.errorComp) 0 = Left "Cannot divide by zero"
erronious = Refl

----------------------------------- Ask -----------------------------------

data Ask : (r : Type) -> (a : Type) -> Type where
  MkAsk : Ask r r

||| Request a value of the environment.
ask : Member (Ask r) effs => Eff effs r
ask = send MkAsk

covering
||| Handler for `Ask` effects.
runAsk : r -> Eff (Ask r :: effs) ~> Eff effs
runAsk r = interpret (\MkAsk => pure r)

||| An example ask computation.
askComp : Member (Ask String) effs => Eff effs String
askComp = do
  name <- ask
  pure $ "Hello " <+> name <+> "!"

asked : (Eff.run . Eff.runAsk "Mike") Eff.askComp = "Hello Mike!"
asked = Refl

--------------------------------- Console ---------------------------------

||| An effect for reading and writing to the console.
data Console : Type -> Type where
  ReadLine : Console String
  PrintLine : String -> Console ()

readLine : Member Console effs => Eff effs String
readLine = send ReadLine

printLine : Member Console effs => String -> Eff effs ()
printLine = send . PrintLine

||| An example console computation.
consoleComp : Member Console effs => Eff effs ()
consoleComp = do
  printLine "Enter your name:"
  name <- readLine
  printLine $ "Hello " ++ name ++ ". Welcome!"

covering
||| Handler for `Console` effects.
runConsole : Eff [Console, IO] ~> IO
runConsole = runM . interpretM f
  where
    f : Console ~> IO
    f ReadLine = getLine
    f (PrintLine str) = putStrLn str

--------------------------------- Store ---------------------------------

||| An effect for reading and writing to a store.
data Store : Type -> Type -> Type where
  Get : Store s s
  Put : s -> Store s ()

||| Get a value from the store
get : Member (Store s) effs => Eff effs s
get = send Get

||| Put a new value into the store
put : Member (Store s) effs => s -> Eff effs ()
put = send . Put

||| Modify the current state of type `s : Type` using provided function `(s -> s)`.
modify : Member (Store s) effs => (s -> s) -> Eff effs ()
modify f = map f get >>= put

covering
||| Handler for store effects.
runStore : s -> Eff ((Store s) :: effs) a ->  Eff effs (a, s)
runStore initState = handleRelayS initState (\s, x => pure (x, s)) $ \s, x, k => case x of
  Get => k s s
  Put s' => k s' ()

covering
||| Run a store effect, returning only the final state.
execStore : s -> Eff ((Store s) :: effs) a ->  Eff effs s
execStore s = map snd . runStore s

covering
||| Run a store effect, discarding the final state.
evalStore : s -> Eff ((Store s) :: effs) a ->  Eff effs a
evalStore s = map fst . runStore s

||| An example store computation.
storeComp : Member (Store Nat) effs => Eff effs ()
storeComp = do
  n <- get
  put (S n)

stored : (Eff.run . Eff.execStore 10) Eff.storeComp = the Nat 11
stored = Refl

--------------------------- Combined effects ----------------------------

-- TODO: Implement some combined effects
