module Data.List.Quantifiers.Extra

import public Data.List.Elem
import public Data.List.Quantifiers

%default total

||| Just like `HList` is an alias for `All id`, this is an
||| alias for `Any id`.
public export
0 HSum : List Type -> Type
HSum = Any id

||| Proof that a value is present in a list. This is
||| just an alias for `Data.List.Elem` with a name that's
||| sometimes more fitting.
public export
0 Has : (v : a) -> (vs : List a) -> Type
Has = Elem

||| Removes an element from a list. This is used to
||| calculate the list of effects after a single effect
||| was properly handled.
public export
0 (-) : (ts : List a) -> (v : a) -> (prf : Has v ts) => List a
(-) (_ :: vs)      _ @{Here}    = vs
(-) (y :: x :: xs) v @{There k} = y :: (-) (x :: xs) v

||| Inject a value into a `Any f ts`.
public export %inline
inject : (prf : Has t ts) => f t -> Any f ts
inject @{Here}    v = Here v
inject @{There _} v = There $ inject v

||| Tries to extract a value from a `Any f ts`.
public export
project : (prf : Has t ts) => Any f ts -> Maybe (f t)
project @{Here}    (Here v)  = Just v
project @{There p} (There v) = project @{p} v
project _                    = Nothing

||| Extracts the only possible value from a unary sum.
public export
project1 : Any f [t] -> f t
project1 (Here v)  = v
project1 (There _) impossible

||| Extract one of the values from an `Any f ts`.
public export
decomp :
     {0 t      : k}
  -> {0 ts     : List k}
  -> {auto prf : Has t ts}
  -> Any f ts
  -> Either (Any f (ts - t)) (f t)
decomp @{Here}                       (Here v)  = Right v
decomp @{Here}                       (There v) = Left $ v
decomp @{There _} {ts = _ :: _ :: _} (Here v)  = Left $ Here v
decomp @{There _} {ts = _ :: _ :: _} (There v) = mapFst There $ decomp v

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

export
All (Eq . p) xs => Eq (All p xs) where
  (==)           [] []             = True
  (==) @{_ :: _} (h1::t1) (h2::t2) = h1 == h2 && t1 == t2

%hint
allEq : All (Ord . p) xs => All (Eq . p) xs
allEq @{[]}     = []
allEq @{_ :: _} = %search :: allEq

export
All (Ord . p) xs => Ord (All p xs) where
  compare            [] []            = EQ
  compare @{_ :: _} (h1::t1) (h2::t2) = case compare h1 h2 of
    EQ => compare t1 t2
    o  => o

export
All (Eq . p) xs => Eq (Any p xs) where
  (==) @{_ :: _} (Here x)  (Here y)  = x == y
  (==) @{_ :: _} (There x) (There y) = x == y
  (==) _ _ = False

export
All (Ord . p) xs => Ord (Any p xs) where
  compare @{_ :: _} (Here x)  (Here y)  = compare x y
  compare @{_ :: _} (There x) (There y) = compare x y
  compare           (Here _)  (There _) = LT
  compare           (There _) (Here _)  = GT

export
All (Semigroup . p) xs => Semigroup (All p xs) where
  (<+>)           [] [] = []
  (<+>) @{_ :: _} (h1::t1) (h2::t2) = (h1 <+> h2) :: (t1 <+> t2)

%hint
allSemigroup : All (Monoid . p) xs => All (Semigroup . p) xs
allSemigroup @{[]}     = []
allSemigroup @{_ :: _} = %search :: allSemigroup

export
All (Monoid . p) xs => Monoid (All p xs) where
  neutral @{[]}   = []
  neutral @{_::_} = neutral :: neutral
