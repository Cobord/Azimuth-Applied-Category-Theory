import qualified Math.Combinatorics.Poset as PS
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

--fLStar 

--fLShriek