module Examples

import Eff

%default total

---------------------------------- Abort ----------------------------------
namespace Abort
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

  notAborted : (I.run . Abort.runAbort . Abort.abortComp) [0, 2] = Just [0, 2]
  notAborted = Refl

  aborted : (I.run . Abort.runAbort . Abort.abortComp) [0, 1, 2] = Nothing
  aborted = Refl

---------------------------------- Error ----------------------------------
namespace Error
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
  noError : (I.run . Error.runError . Error.errorComp) 5 = the (Either String Int) (Right 2)
  noError = Refl

  erronious : (I.run . Error.runError . Error.errorComp) 0 = Left "Cannot divide by zero"
  erronious = Refl

----------------------------------- Ask -----------------------------------
namespace Ask
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

  asked : (I.run . Ask.runAsk "Mike") Ask.askComp = "Hello Mike!"
  asked = Refl

--------------------------------- Console ---------------------------------
namespace Console
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
namespace Store
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

  stored : (I.run . Store.execStore 10) Store.storeComp = the Nat 11
  stored = Refl

--------------------------- Combined effects ----------------------------

-- TODO: Implement some combined effects
