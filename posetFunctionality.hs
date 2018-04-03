import qualified Math.Combinatorics.Poset as PS

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

-- placeholder for Galois connections
leftAdjoint:: (PS.Poset t1 -> PS.Poset t2) -> (PS.Poset t2 -> Maybe (PS.Poset t1))
leftAdjoint f a = Nothing

rightAdjoint:: (PS.Poset t1 -> PS.Poset t2) -> (PS.Poset t2 -> Maybe (PS.Poset t1))
rightAdjoint f a = Nothing