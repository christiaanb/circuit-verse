{- | Circuit implementation of https://dl.acm.org/doi/10.1145/3607845

The Verse Calculus: A Core Calculus for Deterministic Functional Logic Programming
-}
module CircuitVerse where

import Clash.Prelude hiding (all, or)
import Clash.Annotations.TH
import qualified Data.Foldable as F
import Data.Maybe
import Data.Monoid

type Variable = String

data Expression
  = V Value
  | S Equation Expression
  | E Variable Expression
  | Or Expression Expression
  | App Value Value
  | One Expression
  | All Expression
  deriving Show

data Equation
  = Expr Expression
  | Eqn Value Expression
  deriving Show

data Value
  = Var Variable
  | K Int
  | GT
  | ADD
  | Tup [Value]
  | Lam Variable Expression
  deriving Show

-- | Invariant: Just values occur left-most in the vector
--
-- <>         = (0,repeat Nothing)
-- fail       = (1,singleton Nothing)
-- v          = (1,singleton (Just v))
-- <v1,v2,..> = (n,Just v1 :> Just v2 :> ...)
type Values n = (Word, Vec n (Maybe Int))

one :: forall n . (1 <= n, KnownNat n) => Values n -> Values 1
one (0,_)  = (0,singleton Nothing)
one (_,xs) = (1,singleton (getFirst (foldMap First xs)))

all :: forall n . (1 <= n, KnownNat n) => Values n -> Values n
all (n,xs) = case getFirst (foldMap First xs) of
  Nothing -> (0,xs)
  _       -> (n,xs)

or :: forall n1 n2 . (KnownNat n1, KnownNat n2) => Values n1 -> Values n2 -> Values (n1 + n2)
or (n1,v1) (n2,v2) = (n1+n2, map go (iterateI go2 (n1,n2)))
  where
    go (0,0) = Nothing
    go (0,x) = v2 !! (length v2 - fromIntegral x)
    go (x,_) = v1 !! (length v1 - fromIntegral x)

    go2 (0,0) = (0,0)
    go2 (0,n) = (0,n-1)
    go2 (x,y) = (x-1,y)

add :: Values 2 -> Values 1
add (2,Cons (Just x) (Cons (Just y) Nil)) = (1, Cons (Just (x + y)) Nil)
add _ = (1,Cons Nothing Nil)

gt :: Values 2 -> Values 1
gt (2,Cons (Just x) (Cons (Just y) Nil)) | x > y = (1, Cons (Just x) Nil)
gt _ = (1,Cons Nothing Nil)

eqn ::  KnownNat n => Values n -> Values n -> Values n
eqn n m = if n == m then m else (1,repeat Nothing)

comp :: (1 <= n, KnownNat n, KnownNat m) => Values n -> Values m -> Values m
comp (0,_) v = v
comp (_,xs) v
  | F.all isNothing xs = (1,repeat Nothing)
  | otherwise          = v

apply :: KnownNat n => Values n -> Values n
apply (0,_) = (1,repeat Nothing)
apply v = v

nth :: KnownNat n => Values n -> Word -> Values 1
nth (_,xs) n = (1,singleton (xs !! n))

int :: Int -> Values 1
int i = (1,singleton (Just i))



-- \p.E a.p = <a,1>;a
progFirst :: Expression
progFirst
  = V (Lam "p" (E "a" (S (Eqn (Var "p") (V (Tup [Var "a", K 1]))) (V (Var "a")))))

circFirst ::
  "args" ::: Values 2 ->
  "res" ::: Values 1
circFirst =
  \p -> comp (eqn p (nth p 0 `or` int 1)) (nth p 0)
makeTopEntity 'circFirst
