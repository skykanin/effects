||| An implementation of an extensible effect system based on freer monads
||| which leverages dependent types to enforce invariants in a type safe manner.
||| Sources:
|||  - https://okmij.org/ftp/Haskell/extensible/more.pdf
|||  - https://hackage.haskell.org/package/freer-simple-1.2.1.2
module Eff

import public Internal as I
import public Union
import public Util

%default total

covering
public export
||| The simplest way to produce an effect handler. Given a natural
||| transformation from some effect `eff` to some effectful computation with
||| effects `effs`, produces a natural transformation from `Eff (eff :: effs)`
||| to `'Eff effs`.
interpret : (eff ~> Eff effs) -> (Eff (eff :: effs) ~> Eff effs)
interpret f = handleRelay pure (\e => (f e >>=))

public export
||| "Sends" an effect, which should be a value defined as part of an effect
||| algebra, to an effectful computation. This is used to connect the definition
||| of an effect to the `Eff` monad so that it can be used and handled.
send : Member eff effs => eff a -> Eff effs a
send t = Impure (inj t) (tsingleton Pure)

export
||| Identical to send, but specialised to the final effect in effs to assist type inference.
sendM : (Monad m, LastMember m effs) => m a -> Eff effs a
sendM = send

covering
export
||| Like interpret, this function runs an effect without introducing another one.
||| However, this runs the effect in a final monad in effs, intended to be run with `runM`.
interpretM : (Monad m, LastMember m effs) => (eff ~> m) -> Eff (eff :: effs) ~> Eff effs
interpretM f = interpret (sendM . f)

covering
export
||| Like `interpret`, but instead of removing the interpreted effect `eff1`, reencodes it in
||| some new effect `eff2`.
reinterpret : (eff1 ~> Eff (eff2 :: effs)) -> Eff (eff1 :: effs) ~> Eff (eff2 :: effs)
reinterpret f = replaceRelay pure (\e => (f e >>=))
