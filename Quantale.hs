{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds, TypeSynonymInstances, TypeFamilies, TypeOperators #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}

module Quantale where

import qualified Data.Set as Set
--import qualified Data.Number.Fin.Integer as Fin
import Data.Maybe

class UnitalQuantale a where
    unit :: a
    po :: a -> a -> Bool
    monoidal :: a -> a -> a
    myJoin :: [a] -> a

-- change int to other numeric types if desired, Nothing stands for +\infty
type Cost = Maybe Int

greatestLowerBound :: Cost -> Cost -> Cost
greatestLowerBound Nothing x = x
greatestLowerBound x Nothing = x
greatestLowerBound (Just x) (Just y)
                                    | x<=y = Just x
                                    | otherwise = Just y

instance UnitalQuantale Cost where
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