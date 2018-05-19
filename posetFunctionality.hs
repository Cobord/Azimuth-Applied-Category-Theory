{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds, TypeFamilies, TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import qualified Math.Combinatorics.Poset as PS
import qualified Math.Combinat.Partitions.Set as SetPart
import qualified Data.Set as Set

-- biggerThanAll p z xs tells if z is greater than or equal to all x from xs
biggerThanAll:: PS.Poset t1 -> t1 -> [t1] -> Bool
biggerThanAll (PS.Poset (set,po)) z xs = and [z `po` x | x <- xs]

-- upperBounds p xs gives all the elements in poset p such that they are greater than or equal to everything in xs
upperBounds:: PS.Poset t1 -> [t1] -> [t1]
upperBounds (PS.Poset (set,po)) xs = [z | z <- set, biggerThanAll (PS.Poset (set,po)) z xs]

--given the list of upperBounds, an element z of this list may be not a good candidate for least upper bound
-- this happens when z is greater than or equal to an element of the list besides itself. That gives a length > 1
isTooBig:: PS.Poset t1 -> [t1] -> t1 -> Bool
isTooBig (PS.Poset (set,po)) zs z = (length $ [z1 | z1 <- zs , z `po` z1]) > 1

--make the list of upperBounds and then filter away the candidates that are too big
join:: PS.Poset t1 -> [t1] -> [t1]
join (PS.Poset (set,po)) xs = filter (\y -> not $ isTooBig (PS.Poset (set,po)) zs y) zs
                              where zs = upperBounds (PS.Poset (set,po)) xs

-- Test functionality of join by using the poset of divisors 24
example :: [Int] -> [Int]
example xs = join (PS.dual $ PS.posetD 24) xs

-- flip everything upside down
meet:: PS.Poset t1 -> [t1] -> [t1]
meet p xs = join (PS.dual p) xs

leftAdjointHelper p1@(PS.Poset (p1Set,p1po)) p2@(PS.Poset (p2Set,p2po)) g p = show [q | q <- p1Set , (g q) `p2po` p]

-- assume g is a right adjoint of something, find it's left adjoint
leftAdjoint:: PS.Poset t1 -> PS.Poset t2 -> (t1 -> t2) -> t2 -> [t1]
leftAdjoint p1@(PS.Poset (p1Set,p1po)) p2@(PS.Poset (p2Set,p2po)) g p = meet p1 qs
                                                                     where qs = [q | q <- p1Set , (g q) `p2po` p]

rightAdjointHelper p1@(PS.Poset (p1Set,p1po)) p2@(PS.Poset (p2Set,p2po)) f q = show [p | p <- p1Set , q `p2po` (f p)]

-- assume f is a left adjoint of something, find it's right adjoint
rightAdjoint:: PS.Poset t1 -> PS.Poset t2 -> (t1 -> t2) -> t2 -> [t1]
rightAdjoint p1@(PS.Poset (p1Set,p1po)) p2@(PS.Poset (p2Set,p2po)) f q = join p1 [p | p <- p1Set , q `p2po` (f p)]

-- Exercise 1.77
data SimpleExample = Zero | One | Two deriving (Show,Eq)
simpleExampleOrder Zero _ = True
simpleExampleOrder One One = True
simpleExampleOrder One Two = True
simpleExampleOrder Two Two = True
simpleExampleOrder _ _ = False
simpleExamplePoset = PS.dual ( PS.Poset ([Zero,One,Two],simpleExampleOrder) )
sampleF Zero = Zero
sampleF One = Zero
sampleF Two = Two

myPowerset :: (Ord a) => Set.Set a -> Set.Set (Set.Set a)
myPowerset s = Set.fromList $ map (Set.fromList) (powerList $ Set.toList s)
powerList :: [a] -> [[a]]
powerList [] = [[]]
powerList (x:xs) = powerList xs ++ map (x:) (powerList xs)

-- give the poset structure of such a poset
-- the implementation in Data.Set uses total order on X and Y
powerSetPoset :: Ord a => Set.Set a -> PS.Poset (Set.Set a)
powerSetPoset xs = PS.dual $ PS.Poset (Set.elems $ myPowerset xs,Set.isSubsetOf)

fUStar :: (Ord a1, Ord a2) => (a1 -> a2) -> Set.Set a1 -> Set.Set a2 -> Set.Set a1
fUStar f xSet ys = Set.fromList [x | x <- Set.toList xSet , Set.member (f x) ys]

--should only be one set in the output list, but can't guarantee that because left and right adjoint output lists
fLStar :: (Ord a1, Ord a2) => (a1 -> a2) -> Set.Set a1 -> Set.Set a2 -> Set.Set a1 -> [Set.Set a2]
fLStar f xSet ySet xs = rightAdjoint (powerSetPoset ySet) (powerSetPoset xSet) (\ys -> (fUStar f xSet ys)) xs

--should only be one set in the output list, but can't guarantee that because left and right adjoint output lists
fLShriek :: (Ord a1, Ord a2) => (a1 -> a2) -> Set.Set a1 -> Set.Set a2 -> Set.Set a1 -> [Set.Set a2]
fLShriek f xSet ySet xs = leftAdjoint (powerSetPoset ySet) (powerSetPoset xSet) (\ys -> (fUStar f xSet ys)) xs

--Exercise 1.95
exampleYSet = Set.fromList [1,2,3,4]
exampleXSet = Set.fromList [5,6]
exampleFunction 5 = 2
exampleFunction 6 = 2
exampleB1 = Set.fromList [1,2,3]
exampleB2 = Set.fromList [1,3]
exampleA1 = Set.fromList [6]
exampleA2 = Set.fromList [5,6]
parta1 = fUStar exampleFunction exampleXSet exampleB1
parta2 = fUStar exampleFunction exampleXSet exampleB2
partb1 = fLShriek exampleFunction exampleXSet exampleYSet exampleA1
partb2 = fLShriek exampleFunction exampleXSet exampleYSet exampleA2
partc1 = fLStar exampleFunction exampleXSet exampleYSet exampleA1
partc2 = fLStar exampleFunction exampleXSet exampleYSet exampleA2

--partition Logic
compareSetPartitions :: SetPart.SetPartition -> SetPart.SetPartition -> Bool
compareSetPartitions sp1 sp2 = and [isXSubset (Set.fromList x) sp1 | x <- SetPart.fromSetPartition sp2 ] where 
                               isXSubset x1 sp1' = or [ Set.isSubsetOf x1 (Set.fromList y) | y <- SetPart.fromSetPartition sp1' ]
partitionPoset :: Int -> PS.Poset SetPart.SetPartition
partitionPoset n = PS.Poset (SetPart.setPartitions n, compareSetPartitions)

--TODO: fUStar and fLShriek but this one has no fLStar

--free commutative monoidal preorder without any reactions

data Nat = Z | S Nat deriving (Show)

data SNat n where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

data Vector a n where
  Nil  :: Vector a Z
  (:-) :: a -> Vector a n -> Vector a (S n)
infixr 5 :-

deriving instance Eq a => Eq (Vector a n)

toList :: Vector a n -> [a]
toList Nil = []
toList (x :- xs) = x : toList xs
instance Show a => Show (Vector a n) where
  showsPrec d = showsPrec d . toList

myReplicate :: SNat n -> a -> Vector a n
myReplicate SZ     _ = Nil
myReplicate (SS n) a = a :- myReplicate n a
--takes a natural number n and a list of integers and puts them into a vector of length n
-- default to 0 if the list is too short
fromList:: SNat n -> [Int] -> Vector Int n
fromList SZ _ = Nil
fromList (SS n) [] = myReplicate (SS n) (0)
fromList (SS n) (x:xs) = x :- (fromList n xs)

-- takes an occupied natural number for the number of items like possible chemicals in a complex
-- and a maximum number to say there are at most maxAmount of any one of them
-- and produce the poset with no reactions only the product order
noReactionsSet :: SNat n -> Int -> [Vector Int n]
noReactionsSet SZ _ = [Nil]
noReactionsSet (SS x) maxAmount = [x1 :- y | x1 <- [0..maxAmount], y <- (noReactionsSet x maxAmount)]

-- reversed because can throw away from 4 to get to 3, so 4 <= 3 in reachability ordering
productOrder :: Ord a => Vector a n -> Vector a n -> Bool
productOrder Nil Nil = True
productOrder (x:-xs) (y:-ys) = (y<=x) && productOrder xs ys

noReactionsPoset :: SNat n -> Int -> PS.Poset (Vector Int n)
noReactionsPoset numItems maxAmount = PS.Poset (mySet,productOrder) where mySet=(noReactionsSet numItems maxAmount)