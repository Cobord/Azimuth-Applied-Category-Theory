{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds, TypeSynonymInstances, TypeFamilies, TypeOperators #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}

module Quantale where

import qualified Data.Set as Set
import qualified Math.Combinatorics.Poset as PS
import Data.Maybe

class UnitalQuantale a where
    unit :: a
    po :: a -> a -> Bool
    monoidal :: a -> a -> a
    myJoin :: [a] -> a

-- change int to other numeric types if desired, Nothing stands for +\infty
type Cost = Maybe Int

-- the default instance of Ord that comes from Maybe n with (Ord n) puts Nothing <= everything
-- we want it to be >= everything

greatestLowerBound :: (Ord a) => Maybe a -> Maybe a -> Maybe a
greatestLowerBound Nothing x = x
greatestLowerBound x Nothing = x
greatestLowerBound (Just x) (Just y)
                                    | x<=y = Just x
                                    | otherwise = Just y

instance (Num a, Ord a) => UnitalQuantale (Maybe a) where
    po Nothing Nothing = True
    po Nothing (Just x) = True
    po (Just x) Nothing = False
    po (Just x) (Just y) = (x >= y)
    monoidal _ Nothing = Nothing
    monoidal Nothing _ = Nothing
    monoidal (Just x) (Just y) = Just (x+y)
    unit = Just 0
    myJoin [] = Nothing
    myJoin (x:xs) = greatestLowerBound x (myJoin xs)

reachability :: Num a => Maybe a -> Bool
reachability (Just x) = True
reachability Nothing = False

-- power set of strings
data Letters = Alpha | Beta | Gamma deriving (Eq,Read,Show,Ord)
type PowerSetStrings = Set.Set [Letters]
instance UnitalQuantale PowerSetStrings where
    po a b = b `Set.isSubsetOf` a
    monoidal a b = Set.fromList [fromA++fromB | fromA <- Set.toList a, fromB <- Set.toList b]
    unit = Set.fromList []
    myJoin = Set.unions

multiplyQMatrices :: (UnitalQuantale q) => [b] -> (a -> b -> q) -> (b -> c -> q) -> a -> c -> q
multiplyQMatrices allY matrixM matrixN x z = myJoin [monoidal (matrixM x y) (matrixN y z) | y <- allY]

powerQMatrices :: (Eq a,UnitalQuantale q) => [a] -> (a -> a -> q) -> Int -> a -> a -> q
powerQMatrices allX matrixM n x y
               | n <= 0 = myJoin []
               | n == 0 && (x==y) = unit
               | n == 0 && (x/=y) = myJoin []
               | n == 1 = matrixM x y
               | n > 1 = multiplyQMatrices allX matrixM (powerQMatrices allX matrixM (n-1)) x y

-- In 7 sketches this is on page 62 
data MyVertices = VertexX | VertexY | VertexZ deriving (Eq,Read,Show)
allVertices = [VertexX , VertexY , VertexZ]
weightGraph :: MyVertices -> MyVertices -> Cost
weightGraph VertexX VertexX = unit
weightGraph VertexX VertexY = Just 4
weightGraph VertexX VertexZ = Just 3
weightGraph VertexY VertexY = unit
weightGraph VertexY VertexX = Just 3
weightGraph VertexZ VertexZ = unit
weightGraph VertexZ VertexY = Just 4
weightGraph _ _ = Nothing

-- the Z, X entry of M_Y^2 in notation of 7Sketches
example = multiplyQMatrices allVertices weightGraph weightGraph VertexZ VertexX
-- all of the entries M_Y^3 read into a single list instead of a matrix
example2 = [powerQMatrices allVertices weightGraph 3 x y|x<-allVertices, y<-allVertices]

-- category enriched in a quantale especially cost enriched, feasibility relations with costs

-- Eq t, UnitalQuantale q is not enforced when creating a QuantaleEnriched, unless you do it through the below two functions 
newtype QuantaleEnriched t q = QuantaleEnriched {myData :: ([t],t->t->q)}

toQuantaleEnriched :: (Eq t, UnitalQuantale q) => [t] -> (t -> t -> q) -> QuantaleEnriched t q
toQuantaleEnriched underlyingSet morphisms = QuantaleEnriched {myData = (underlyingSet,morphisms)}

toQuantaleEnriched2 :: (Eq t, UnitalQuantale q) => [t] -> (t -> t -> q) -> Int -> QuantaleEnriched t q
toQuantaleEnriched2 allVertices oneStepMorphisms maxSteps = toQuantaleEnriched allVertices (powerQMatrices allVertices oneStepMorphisms maxSteps)

-- same as example2 but wrapped into the newtype
example3 = toQuantaleEnriched2 allVertices weightGraph 5

toPoset :: QuantaleEnriched t q -> (q -> Bool) -> PS.Poset t
toPoset enriched reduction = PS.Poset (set,\x y -> reduction $ poOne x y) where (set,poOne)=(myData enriched)

example4 = toPoset example3 reachability

quantaleCollage :: (Eq a,Eq t, UnitalQuantale q) => Int -> QuantaleEnriched t q -> QuantaleEnriched a q -> (t -> a -> q) -> QuantaleEnriched (Either t a) q
quantaleCollage upperBound enriched1 enriched2 connection = toQuantaleEnriched2 fullSet oneStepMorphisms upperBound
        where setA = fst $ myData enriched1
              setB = fst $ myData enriched2
              morphismsA = snd $ myData enriched1
              morphismsB = snd $ myData enriched2
              fullSet = map Left setA ++ map Right setB
              oneStepMorphisms (Left a1) (Left a2) = morphismsA a1 a2
              oneStepMorphisms (Right b1) (Right b2) = morphismsB b1 b2
              oneStepMorphisms (Left a1) (Right b2) = connection a1 b2
              oneStepMorphisms _ _ = myJoin []

-- example from Lecture 59
-- multiplied by 10 everywhere to keep integers, as an overestimation allowed 5 step paths at most
-- the shortest paths should be within that coarse upper bound, but didn't check
-- Example is untested but compiles
data Example59C = North | South | East | West deriving (Show,Read,Eq)
example59XSet :: [Example59C]
texample59XSet = [North,South,East,West]
example59XMor :: Example59C -> Example59C -> Cost
example59XMor South West = Just 30
example59XMor South East = Just 20
example59XMor West North = Just 10
example59XMor East North = Just 50
example59XMor East South = Just 4
example59XMor _ _ = Nothing
example59CQE :: QuantaleEnriched Example59C Cost
example59CQE = toQuantaleEnriched2 example59XSet example59XMor 5
data Example59D = A | B | C | D | E deriving (Show,Read,Eq)
example59YSet :: [Example59D]
example59YSet = [A,B,C,D,E]
example59YMor :: Example59D -> Example59D -> Cost
example59YMor A B = Just 70
example59YMor A C = Just 0
example59YMor B D = Just 20
example59YMor _ _ = Nothing
example59DQE :: QuantaleEnriched Example59D Cost
example59DQE = toQuantaleEnriched2 example59YSet example59YMor 5
connector :: Example59C -> Example59D -> Cost
connector South A = Just 90
connector East B = Just 120
connector North C = Just 47
connector North E = Just 80
costEnrichedCollage :: QuantaleEnriched (Either Example59C Example59D) Cost
costEnrichedCollage = quantaleCollage 5 example59CQE example59DQE connector