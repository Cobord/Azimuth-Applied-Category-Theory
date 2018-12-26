{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
--{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
--{-# LANGUAGE UndecidableInstances, TypeFamilies, TypeOperators #-}

import Control.Lens
import Data.Tree
import Data.Maybe
import qualified Data.List.NonEmpty as NEL

data PossibleStates = CLOSED | LISTEN | SYN_RCVD | SYN_SENT | 
                      ESTABLISHED | FIN_WAIT_1 | FIN_WAIT_2 |
                      CLOSE_WAIT | CLOSING | LAST_ACK | TIME_WAIT
                      deriving (Eq,Read,Show,Bounded,Enum)


split_list :: [a] -> ([a],[a])
split_list [] = ([],[])
split_list (x:xs) = (x:odd_half,even_half) where (even_half,odd_half)=split_list xs

make_tree_leaf_only :: [a] -> Tree (Maybe a)
make_tree_leaf_only [] = Node{rootLabel=Nothing,subForest=[]}
make_tree_leaf_only [x] = Node{rootLabel=Just x,subForest=[]}
make_tree_leaf_only xs = Node{rootLabel=Nothing,subForest=[make_tree_leaf_only even_half,make_tree_leaf_only odd_half]}
                         where (even_half,odd_half)=(split_list xs)

all_states_leaf_only :: (Bounded a,Enum a) => Tree (Maybe a)
all_states_leaf_only = make_tree_leaf_only [minBound..maxBound]

where_in_tree_helper :: (Bounded a,Enum a,Eq a) => [a] -> a -> [Bool]
where_in_tree_helper all x
                           | all==[x] = [True]
                           | elem x even_half = True:(where_in_tree_helper even_half x)
                           | otherwise = False:(where_in_tree_helper odd_half x)
                           where (even_half,odd_half)=(split_list all)
where_in_tree :: (Bounded a,Enum a,Eq a) => a -> [Bool]
where_in_tree = where_in_tree_helper [minBound..maxBound]
where_in_tree_NEL :: (Bounded a,Enum a,Eq a) => a -> NEL.NonEmpty Bool
where_in_tree_NEL x = (head z) NEL.:| (tail z) where z=where_in_tree x

to_prism_basic True = _Left
to_prism_basic False = _Right
to_prisms x = map to_prism_basic (where_in_tree x)
to_prisms_NEL (x NEL.:| xs) = (to_prism_basic x) NEL.:| (map to_prism_basic xs)
to_prisms2_NEL x = to_prisms_NEL $ where_in_tree_NEL x

nonempty_fold :: NEL.NonEmpty a -> (a -> b -> b) -> (a -> b) -> b
nonempty_fold (x NEL.:| xs) f g = foldr f (g x) xs

apply_one_time ([],x) = ([],x)
apply_one_time ((f:fs),x) = (fs,f x)
repeat_apply :: (a -> a) -> Int -> (a -> a)
repeat_apply f x
                 | x<=1 = f
                 | otherwise=f.(repeat_apply f (x-1))
apply_all [] x = x
apply_all (f:fs) x = apply_all fs (f x)

-- the sort of nested eithers that want
--over _Right (over _Right (+1)) (Right (Left 2))
--over _Right (over _Right (+1)) (Right (Right 2))

from_bool_to_either True = (Left $)
from_bool_to_either False = (Right $)
into_nested_either_helper x= NEL.map from_bool_to_either (where_in_tree_NEL x)
into_nested_eithers x y = (w,z y) where (z NEL.:| w)=(into_nested_either_helper x)
into_nested_eithers2 w z
                        | length w==0=([],z)
                        | otherwise=((tail w),((head w) z))

--into_nested_eithers3 x y = into_nested_eithers2 w z where (w,z)=into_nested_eithers x y