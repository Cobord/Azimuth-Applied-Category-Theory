{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds, TypeFamilies, TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.List.Split

data Nat = Z | S Nat deriving (Show)

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

data OpCodes = Identity | Read1 | Write1 | Read1Write2 | Add12Put3 | Mult12Put3 | Divide12Put3 | Neg1Put2

arity :: OpCodes -> Int
arity Identity = 0
arity Read1 = 1
arity Write1 = 1
arity Read1Write2 = 2
arity add12Put3 = 3
arity Divide12Put3 = 3
arity Neg1Put2 = 2

data Ordinal (n :: Nat) deriving Eq where
  OZ :: Ordinal (S n)
  OS :: Ordinal n -> Ordinal (S n)

asInteger :: Ordinal n -> Int
asInteger OZ = 0
asInteger (OS x) = 1+ (asInteger x)
  
instance Show (Ordinal n) where
  show x = show asInteger x

sIndex :: Ordinal n -> Vector a n -> a
sIndex OZ     (x :- _)  = x
sIndex (OS n) (_ :- xs) = sIndex n xs

data Resource n = Resource {description::[Char], index::Ordinal n} deriving (Eq,Show)

data Operation n = Operation {name::OpCodes, resourcesAffected::[Resource n]} deriving (Eq,Show)

-- check that an operation code that indicates it should affect n resources
-- does in fact affect n resources
verify :: Operation n -> Bool
verify op = (length $ resourcesAffected op == arity $ name op)

-- if concentrating only on resourcesOfConcern, say if or if not
-- there is any cross talk between resourcesOfConcern and it's complement
-- for convenience call them A and A^c
indicator :: [Ordinal n] -> Operation n -> Bool
indicator resourcesOfConcern op = onlyConcern || onlyComplement where
                                  onlyConcern = and tempList
								  onlyComplement = not $ or tempList
								  tempList = [x `elem` resourcesOfConcern | x <- map index (resourcesAffected op)]

-- break the program into segments based on the parts that can be run
-- in parallel between A and A^c by those that have T for above function
-- punctuated by segments where there is synchronization where function gives F
breakProgramHelper :: [Ordinal n] -> [Operation n] ->  [Bool]
breakProgram resourcesOfConcern = map (indicator resourcesOfConcern)

breakProgram :: [Ordinal n] -> [Operation n] -> [[Operation n]]
breakProgram resourcesOfConcern ops = splitPlaces lengthsList ops where
                                     lengthsList = map length $ split (oneOf [True,False]) (breakProgramHelper resourcesOfConcern ops)

data SNat n where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

-- make a vector of length n filled with same things
replicate :: SNat n -> a -> Vector a n
replicate SZ     _ = Nil
replicate (SS n) a = a :- replicate n a
									 
-- helper functions for historyMonoidLetter
replaceUnaffectedHelper :: Int -> Operation n -> Operation n
replaceUnaffectedHelper i op
                      or [ i==x | x <- map (asInteger.index) (resourcesAffected op)] = op
					  otherwise = Operation (name = Identity, resourcesAffected=[])
replaceUnaffected :: Int -> Vector (Operation n) n -> Vector (Operation n) n
replaceUnaffected _ Nil = Nil
replaceUnaffected indexI x :- xs = (replaceUnaffectedHelper indexI x) :- (replaceUnaffected (1+indexI) xs)

-- elementary history in the https://en.wikipedia.org/wiki/History_monoid
-- but with empty string replaced by the name Identity
historyMonoidLetter :: SNat n -> Operation n -> Vector (Operation n) n
historyMonoidLetter myN op = replaceUnaffected 0 (replicate myN op)
-- global history
historyMonoid :: SNat n -> [Operation n] -> [Vector (Operation n) n]
historyMonoid myN = map (historyMonoidLetter myN)
-- give local histories, if resourcesOfConcern is a singleton this is individual histories
projectToFactors :: [Ordinal n] -> Vector (Operation n) n -> [Operation n]
projectToFactors resourcesOfConcern myHistoryMonoidLetter = [sIndex myN myHistoryMonoidLetter | myN <- resourcesOfConcern]
projectToFactors2 :: [Ordinal n] -> [Vector (Operation n) n] -> [[Operation n]]
projectToFactors2 resourcesOfConcern = map (projectToFactors resourcesOfConcern)