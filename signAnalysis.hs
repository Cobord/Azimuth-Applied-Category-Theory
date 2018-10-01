{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds, TypeSynonymInstances, TypeFamilies, TypeOperators #-}
{-# LANGUAGE UndecidableInstances, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses,FunctionalDependencies #-}

import qualified Data.Set as Set

data Nat = Z | S Nat

convertToNat :: Int -> Nat
convertToNat x
          | x <= 0 = Z
          | otherwise = S (convertToNat (x-1))

type family Plus (n :: Nat) (m :: Nat) :: Nat where
          Plus Z m = m
          Plus (S n) m = S (Plus n m)

data SNat n where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)

instance Show (SNat n) where
  show SZ = "SZ"
  show (SS x) = "SS " ++ (show x)

numericVal :: SNat n -> Integer
numericVal SZ = 0
numericVal (SS x) = 1 + numericVal x

data Signs = Negative | Zero | Positive deriving (Read,Eq,Show,Ord)
data SignsWithCutoff n where
    VeryNegative :: SignsWithCutoff Z
    SlightlyNegative :: SignsWithCutoff Z
    VeryZero :: SignsWithCutoff Z
    SlightlyPositive :: SignsWithCutoff Z
    VeryPositive :: SignsWithCutoff Z
    Succ :: SignsWithCutoff n -> SignsWithCutoff (S n)

data FivePossibilities = Poss1 | Poss2 | Poss3 | Poss4 | Poss5 deriving (Eq,Ord,Enum)
reduceToFive :: SignsWithCutoff n -> FivePossibilities
reduceToFive VeryNegative = Poss1
reduceToFive SlightlyNegative = Poss2
reduceToFive VeryZero = Poss3
reduceToFive SlightlyPositive = Poss4
reduceToFive VeryPositive = Poss5
reduceToFive (Succ x) = reduceToFive x
instance Eq (SignsWithCutoff n) where
    x == y = (reduceToFive x) == (reduceToFive y)
instance Ord (SignsWithCutoff n) where
    x `compare` y = (reduceToFive x) `compare` (reduceToFive y)

pushCutoffUp :: SNat n -> SignsWithCutoff m -> SignsWithCutoff (Plus n m)
pushCutoffUp SZ x = x
pushCutoffUp (SS x) y = Succ (pushCutoffUp x y)

data BinaryOperations = Plus | Times | Minus deriving (Read,Eq,Show,Ord)
data UnaryOperations = Negate deriving (Read,Eq,Show,Ord)
data PossibleVariables = PositiveVariable | NonnegativeVariable | NonzeroVariable

getSignVar :: PossibleVariables -> Set.Set Signs
getSignVar PositiveVariable = Set.singleton Positive
getSignVar NonnegativeVariable = Set.fromAscList [Zero,Positive]
getSignVar NonzeroVariable = Set.fromAscList [Negative,Positive]
getSignVarWithCutoff :: SNat n -> PossibleVariables -> Set.Set (SignsWithCutoff (Plus n Z))
getSignVarWithCutoff cutoff PositiveVariable = Set.singleton (pushCutoffUp cutoff SlightlyPositive)
getSignVarWithCutoff cutoff NonnegativeVariable = Set.fromAscList [pushCutoffUp cutoff VeryZero,pushCutoffUp cutoff SlightlyPositive]
getSignVarWithCutoff cutoff NonzeroVariable = Set.fromAscList [pushCutoffUp cutoff SlightlyNegative,pushCutoffUp cutoff SlightlyPositive]

myLiftA2 :: (a -> b -> (a,b)) -> [a] -> [b] -> [(a,b)]
myLiftA2 combine xs ys = [combine x y | x<-xs , y<-ys]
cartesianProduct:: (Ord a,Ord b) => Set.Set a -> Set.Set b -> Set.Set (a,b)
cartesianProduct xs ys = Set.fromList $ myLiftA2 (,) (Set.toList xs) (Set.toList ys)

getSign :: (Num a,Eq a,Ord a) => a -> Signs
getSign x 
         | x>0 = Positive
         | x==0 = Zero
         | x<0 = Negative
getSignWithCutoff :: (Num a,Ord a) => (SNat n) -> a -> SignsWithCutoff (Plus n Z)
getSignWithCutoff cutoff x 
         | x>cutoffVal = pushCutoffUp cutoff VeryPositive
         | x>0 = pushCutoffUp cutoff SlightlyPositive
         | x==0 = pushCutoffUp cutoff VeryZero
         | x<(-1*cutoffVal) = pushCutoffUp cutoff VeryNegative
         | x<0 = pushCutoffUp cutoff SlightlyNegative
        where cutoffVal=(fromInteger $ numericVal cutoff)

coarsenSigns::SignsWithCutoff n -> Signs
coarsenSigns VeryNegative = Negative
coarsenSigns VeryPositive = Positive
coarsenSigns SlightlyNegative = Negative
coarsenSigns SlightlyPositive = Positive
coarsenSigns VeryZero = Zero
coarsenSigns (Succ x) = coarsenSigns x

plusCombineHelper :: (Signs,Signs) -> Set.Set Signs
plusCombineHelper (Positive,Positive) = Set.singleton Positive
plusCombineHelper (Positive,Zero) = Set.singleton Positive
plusCombineHelper (Positive,Negative) = Set.fromAscList [Negative,Zero,Positive]
plusCombineHelper (Zero,x) = Set.singleton x
plusCombineHelper (Negative,Negative) = Set.singleton Negative
plusCombineHelper (x,y) = plusCombineHelper (y,x)

plusCombineHelper2 :: (SignsWithCutoff n,SignsWithCutoff n) -> Set.Set (SignsWithCutoff n)
plusCombineHelper2 (VeryNegative,VeryNegative) = Set.singleton VeryNegative
plusCombineHelper2 (VeryNegative,SlightlyNegative) = Set.singleton VeryNegative
plusCombineHelper2 (VeryNegative,VeryZero) = Set.singleton VeryNegative
plusCombineHelper2 (VeryNegative,SlightlyPositive) = Set.fromAscList [VeryNegative,SlightlyNegative]
plusCombineHelper2 (VeryNegative,VeryPositive) = Set.fromAscList [VeryNegative,SlightlyNegative,VeryZero,SlightlyPositive,VeryPositive]
plusCombineHelper2 (SlightlyNegative,SlightlyNegative) = Set.fromAscList [VeryNegative,SlightlyNegative]
plusCombineHelper2 (SlightlyNegative,VeryZero) = Set.singleton SlightlyNegative
plusCombineHelper2 (SlightlyNegative,SlightlyPositive) = Set.fromAscList [SlightlyNegative,VeryZero,SlightlyPositive]
plusCombineHelper2 (SlightlyNegative,VeryPositive) = Set.fromAscList [SlightlyPositive,VeryPositive]
plusCombineHelper2 (VeryZero,x) = Set.singleton x
plusCombineHelper2 (SlightlyPositive,SlightlyPositive) = Set.fromAscList [SlightlyPositive,VeryPositive]
plusCombineHelper2 (SlightlyPositive,VeryPositive) = Set.singleton VeryPositive
plusCombineHelper2 (VeryPositive,VeryPositive) = Set.singleton VeryPositive
plusCombineHelper2 (Succ x,Succ y) = Set.map Succ (plusCombineHelper2 (x,y))
plusCombineHelper2 (x,y) = plusCombineHelper2 (y,x)

timesCombineHelper :: (Signs,Signs) -> Set.Set Signs
timesCombineHelper (Positive,x) = Set.singleton x
timesCombineHelper (Zero,_) = Set.singleton Zero
timesCombineHelper (Negative,Negative) = Set.singleton Positive
timesCombineHelper (x,y) = timesCombineHelper (y,x)

timesCombineHelper2 :: (SignsWithCutoff n,SignsWithCutoff n) -> Set.Set (SignsWithCutoff n)
timesCombineHelper2 (VeryNegative,VeryNegative) = Set.singleton VeryPositive
timesCombineHelper2 (VeryNegative,SlightlyNegative) = Set.fromAscList [SlightlyPositive,VeryPositive]
timesCombineHelper2 (VeryNegative,VeryZero) = Set.singleton VeryZero
timesCombineHelper2 (VeryNegative,SlightlyPositive) = Set.fromAscList [VeryNegative,SlightlyNegative]
timesCombineHelper2 (VeryNegative,VeryPositive) = Set.singleton VeryNegative
timesCombineHelper2 (SlightlyNegative,SlightlyNegative) = Set.fromAscList [SlightlyPositive,VeryPositive]
timesCombineHelper2 (SlightlyNegative,VeryZero) = Set.singleton VeryZero
timesCombineHelper2 (SlightlyNegative,SlightlyPositive) = Set.fromAscList [VeryNegative,SlightlyNegative]
timesCombineHelper2 (SlightlyNegative,VeryPositive) = Set.fromAscList [VeryNegative,SlightlyNegative]
timesCombineHelper2 (VeryZero,x) = Set.singleton VeryZero
timesCombineHelper2 (SlightlyPositive,SlightlyPositive) = Set.fromAscList [SlightlyPositive,VeryPositive]
timesCombineHelper2 (SlightlyPositive,VeryPositive) = Set.fromAscList [SlightlyPositive,VeryPositive]
timesCombineHelper2 (VeryPositive,VeryPositive) = Set.singleton VeryPositive
timesCombineHelper2 (Succ x,Succ y) = Set.map Succ (timesCombineHelper2 (x,y))
timesCombineHelper2 (x,y) = timesCombineHelper2 (y,x)

negateSign :: Signs -> Signs
negateSign Positive = Negative
negateSign Zero = Zero
negateSign Negative = Positive

minusCombineHelper :: (Signs,Signs) -> Set.Set Signs
minusCombineHelper (x,y) = plusCombineHelper (x,negateSign y)

negateSignCutoff :: SignsWithCutoff n -> SignsWithCutoff n
negateSignCutoff VeryNegative = VeryPositive
negateSignCutoff SlightlyNegative = SlightlyPositive
negateSignCutoff VeryZero = VeryZero
negateSignCutoff SlightlyPositive = SlightlyNegative
negateSignCutoff VeryPositive = VeryNegative
negateSignCutoff (Succ x) = Succ (negateSignCutoff x)

minusCombineHelper2 :: (SignsWithCutoff n,SignsWithCutoff n) -> Set.Set (SignsWithCutoff n)
minusCombineHelper2 (x,y) = plusCombineHelper2 (x,(negateSignCutoff y))

plusCombine :: Set.Set Signs -> Set.Set Signs -> Set.Set Signs
plusCombine x y = Set.unions $ map plusCombineHelper $ Set.toList (cartesianProduct x y)
plusCombine2 :: Set.Set (SignsWithCutoff n) -> Set.Set (SignsWithCutoff n) -> Set.Set (SignsWithCutoff n)
plusCombine2 x y = Set.unions $ map plusCombineHelper2 $ Set.toList (cartesianProduct x y)

timesCombine :: Set.Set Signs -> Set.Set Signs -> Set.Set Signs
timesCombine x y = Set.unions $ map timesCombineHelper $ Set.toList (cartesianProduct x y)
timesCombine2 :: Set.Set (SignsWithCutoff n) -> Set.Set (SignsWithCutoff n) -> Set.Set (SignsWithCutoff n)
timesCombine2 x y = Set.unions $ map timesCombineHelper2 $ Set.toList (cartesianProduct x y)

minusCombine :: Set.Set Signs -> Set.Set Signs -> Set.Set Signs
minusCombine x y = Set.unions $ map minusCombineHelper $ Set.toList (cartesianProduct x y)
minusCombine2 :: Set.Set (SignsWithCutoff n) -> Set.Set (SignsWithCutoff n) -> Set.Set (SignsWithCutoff n)
minusCombine2 x y = Set.unions $ map minusCombineHelper2 $ Set.toList (cartesianProduct x y)

generalOpCombine :: BinaryOperations -> Set.Set Signs -> Set.Set Signs -> Set.Set Signs
generalOpCombine Plus x y = Set.unions $ map plusCombineHelper $ Set.toList (cartesianProduct x y)
generalOpCombine Times x y = Set.unions $ map timesCombineHelper $ Set.toList (cartesianProduct x y)
generalOpCombine Minus x y = Set.unions $ map minusCombineHelper $ Set.toList (cartesianProduct x y)
generalOpCombine2 :: BinaryOperations -> Set.Set (SignsWithCutoff n) -> Set.Set (SignsWithCutoff n) -> Set.Set (SignsWithCutoff n)
generalOpCombine2 Plus x y = Set.unions $ map plusCombineHelper2 $ Set.toList (cartesianProduct x y)
generalOpCombine2 Times x y = Set.unions $ map timesCombineHelper2 $ Set.toList (cartesianProduct x y)
generalOpCombine2 Minus x y = Set.unions $ map minusCombineHelper2 $ Set.toList (cartesianProduct x y)

data Expression a = ValueNode {leafLabel :: a} | BinaryNode { rootLabel2 :: BinaryOperations , leftSubTree :: Expression a, rightSubTree :: Expression a}
                    | UnaryNode {rootLabel1 :: UnaryOperations, subTree :: Expression a} | VariableNode {variableName :: PossibleVariables}

getSign2 :: (Num a,Eq a,Ord a) => Expression a -> Set.Set Signs
getSign2 ValueNode {leafLabel=x} = Set.singleton (getSign x)
getSign2 BinaryNode {rootLabel2=opCode,leftSubTree=z,rightSubTree=w} = generalOpCombine opCode (getSign2 z) (getSign2 w)
getSign2 UnaryNode {rootLabel1=Negate,subTree=z} = Set.map negateSign (getSign2 z)
getSign2 VariableNode {variableName=x} = getSignVar x

getSign3 :: (Num a,Ord a) => (SNat n) -> Expression a -> Set.Set (SignsWithCutoff (Plus n Z))
getSign3 cutoff (ValueNode {leafLabel=x}) = Set.singleton (getSignWithCutoff cutoff x)
getSign3 cutoff (BinaryNode {rootLabel2=opCode,leftSubTree=z,rightSubTree=w}) = generalOpCombine2 opCode (getSign3 cutoff z) (getSign3 cutoff w)
getSign3 cutoff (UnaryNode {rootLabel1=Negate,subTree=z}) = Set.map negateSignCutoff (getSign3 cutoff z)
getSign3 cutoff (VariableNode {variableName=x}) = getSignVarWithCutoff cutoff x