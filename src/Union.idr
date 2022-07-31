module Union

%default total

||| A proof that the type constructor `f` is a member of the
||| type constructor list `fs`.
public export
data Member : (f : Type -> Type) -> (fs : List (Type -> Type)) -> Type where
  Here : Member f (f :: fs)
  There : Member f fs -> Member f (g :: fs)

export
||| A shorthand constraint that represents a combination of multiple 'Member'
||| constraints.
Members : List (Type -> Type) -> List (Type -> Type) -> Type
Members [] effs = ()
Members (x :: xs) effs = Member x effs => Members xs effs

||| Like `Member` except `f` must now be the *last* member of `fs`.
public export
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
public export
data Union : (effs : List (Type -> Type)) -> (x : Type) -> Type where
  Element : Member eff effs -> (v : eff x) -> Union effs x

public export
inj : (ix : Member eff effs) => (v : eff a) -> Union effs a
inj v = Element ix v

export
prj : (ix : Member eff effs) => Union effs a -> Maybe (eff a)
prj {ix = Here} (Element Here v)= Just v
prj {ix = There _} (Element (There x) v)= prj $ Element x v
prj _ = Nothing

public export
decomp : Union (t :: r) a -> Either (Union r a) (t a)
decomp (Element Here v) = Right v
decomp (Element (There x) v) = Left (Element x v)

export
extract : Union [t] a -> t a
extract (Element Here a) = a

export
||| Inject whole `Union r` into a weaker `Union (a :: r)` that has one more summand.
weaken : Union r a -> Union (e :: r) a
weaken (Element p v) = Element (There p) v
