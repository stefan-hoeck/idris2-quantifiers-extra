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
public export
inject : (prf : Has t ts) => f t -> Any f ts
inject @{Here}    v = Here v
inject @{There _} v = There $ inject v

||| Tries to extract a value from a `Any f ts`.
public export
project : (0 t : k) -> (prf : Has t ts) => Any f ts -> Maybe (f t)
project t @{Here}    (Here v)  = Just v
project t @{There p} (There v) = project t @{p} v
project t _                    = Nothing

||| Tries to extract a value from a `Any f ts`.
public export %inline
project' : (prf : Has t ts) => Any f ts -> Maybe (f t)
project' = project t

||| Extracts the only possible value from a unary sum.
public export %inline
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
--          Heterogeneous maps and traversals
--------------------------------------------------------------------------------

namespace Any
  public export %inline
  hmap : ({0 v : k} -> f v -> g v) -> Any f ks -> Any g ks
  hmap = mapProperty

  public export
  hzipWith :
       ({0 v : k} -> f v -> g v -> h v)
    -> All f ks
    -> Any g ks
    -> Any h ks
  hzipWith fun (v :: vs) (Here x)  = Here (fun v x)
  hzipWith fun (v :: vs) (There x) = There $ hzipWith fun vs x

  public export
  collapse : ({0 v : k} -> f v -> x) -> Any f ks -> x
  collapse g (Here v)  = g v
  collapse g (There v) = collapse g v

  public export %inline
  collapse' : Any (Prelude.const x) ks -> x
  collapse' = collapse id

  public export
  hsequence : Applicative f => Any (f . g) ks -> f (Any g ks)
  hsequence (Here x)  = Here <$> x
  hsequence (There x) = There <$> hsequence x

namespace All
  public export %inline
  hmap : ({0 v : k} -> f v -> g v) -> All f ks -> All g ks
  hmap = mapProperty

  public export
  hzipWith :
       ({0 v : k} -> f v -> g v -> h v)
    -> All f ks
    -> All g ks
    -> All h ks
  hzipWith fun (x :: xs) (y :: ys)  = fun x y :: hzipWith fun xs ys
  hzipWith fun []        []         = []

  public export
  hpure : All (Prelude.const ()) ks => ({0 v : k} -> f v) -> All f ks
  hpure @{[]}     fun = []
  hpure @{_ :: _} fun = fun :: hpure fun

  public export
  hfoldl : ({0 v : k} -> acc -> f v -> acc) -> acc -> All f ks -> acc
  hfoldl g x []        = x
  hfoldl g x (y :: ys) = hfoldl g (g x y) ys

  public export %inline
  hfoldMap : Monoid m => ({0 v : k} -> f v -> m) -> All f ks -> m
  hfoldMap g = hfoldl (\x,v => x <+> g v) neutral

  public export
  hsequence : Applicative f => All (f . g) ks -> f (All g ks)
  hsequence []      = pure []
  hsequence (x::xs) = [| x :: hsequence xs |]

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

%hint
allEq : All (Ord . p) xs => All (Eq . p) xs
allEq @{[]}     = []
allEq @{_ :: _} = %search :: allEq

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
