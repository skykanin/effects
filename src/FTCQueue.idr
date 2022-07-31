module FTCQueue

%default total

||| Non-empty tree. Deconstruction operations make it more and more left-leaning.
public export
data FTCQueue : (m : Type -> Type) -> (a, b : Type) -> Type where
  Leaf : (a -> m b) -> FTCQueue m a b
  Node : FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b

public export
||| Build a leaf from a single operation. [O(1)]
tsingleton : (a -> m b) -> FTCQueue m a b
tsingleton = Leaf

infixl 1 |>
public export
||| Append an operation to the right of the tree. [O(1)]
(|>) : FTCQueue m a x -> (x -> m b) -> FTCQueue m a b
t |> r = Node t (Leaf r)

infixr 6 ><
public export
||| Append two trees of operations. [O(1)]
(><) : FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b
t1 >< t2 = Node t1 t2

infixl 4 :|
||| Left view deconstruction data structure.
public export
data ViewL : (m : Type -> Type) -> (a, b : Type) -> Type where
  TOne : (a -> m b) -> ViewL m a b
  (:|) : (a -> m x) -> (FTCQueue m x b) -> ViewL m a b

||| Left view deconstruction. [average O(1)]
public export
tviewl : FTCQueue m a b -> ViewL m a b
tviewl (Leaf r)     = TOne r
tviewl (Node t1 t2) = go t1 t2
  where
    go : FTCQueue m a x -> FTCQueue m x b -> ViewL m a b
    go (Leaf r)       tr = r :| tr
    go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)
