{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE LiberalTypeSynonyms #-}

import Data.Profunctor
import Control.Applicative

data PolymorphicLens s1 s2 a1 a2 = PolymorphicLens{
    get :: s1-> a1,
    put :: s1->a2->s2
}

type Limits a = Limits' a a
data Limits' a b = Limits
    { step :: a -> (b, b)
    , check :: a -> a -> Bool } 

on :: (b -> b -> c) -> (a -> b) -> (a -> a -> c)
on check g x y = check (g x) (g y)

instance Profunctor Limits' where
    dimap g h lim1 = Limits
        { step = (\z -> (h $ fst $ ((step lim1) $ g z),h $ snd $ ((step lim1) $ g z)))
        , check = (check lim1) `on` g }

data PolymorphicLens2 s2 a2 s1 a1 = PolymorphicLens2{
    get2 :: s1 -> a1,
    put2 :: s1 -> a2 -> s2
}
data PolymorphicLens3 a1 a2 s1 s2 = PolymorphicLens3{
    get3 :: s1 -> a1,
    put3 :: s1 -> a2 -> s2
}

identity_conversion_12 :: PolymorphicLens s1 s2 a1 a2 -> PolymorphicLens2 s2 a2 s1 a1
identity_conversion_12 lens1 = PolymorphicLens2{get2=(get lens1),put2=(put lens1)}
identity_conversion_21 :: PolymorphicLens2 s2 a2 s1 a1 -> PolymorphicLens s1 s2 a1 a2
identity_conversion_21 lens2 = PolymorphicLens{get=(get2 lens2),put=(put2 lens2)}

identity_conversion_13 :: PolymorphicLens s1 s2 a1 a2 -> PolymorphicLens3 a1 a2 s1 s2
identity_conversion_13 lens1 = PolymorphicLens3{get3=(get lens1),put3=(put lens1)}
identity_conversion_31 :: PolymorphicLens3 a1 a2 s1 s2 -> PolymorphicLens s1 s2 a1 a2
identity_conversion_31 lens3 = PolymorphicLens{get=(get3 lens3),put=(put3 lens3)}

instance Profunctor (PolymorphicLens2 s2 a2) where
    dimap f g lens2 = PolymorphicLens2{get2 = g . (get2 lens2) . f, put2 = (put2 lens2) . f}

instance Profunctor (PolymorphicLens3 a1 a2) where
    dimap f g lens3 = PolymorphicLens3{get3 = (get3 lens3) . f, put3 = (\x y -> g $ (put3 lens3) (f x) y)}

trimap :: (s1_prime -> s1) -> (a1 -> a1_prime) -> (s2 -> s2_prime) -> (PolymorphicLens s1 s2 a1 a2) -> (PolymorphicLens s1_prime s2_prime a1_prime a2)
trimap f g h lens1 = identity_conversion_31 (dimap (id) (h) (identity_conversion_13 first_convert)) where
                    first_convert = identity_conversion_21 (dimap f g (identity_conversion_12 lens1))

type MonomorphicLens s a = PolymorphicLens s s a a

compose_lenses :: PolymorphicLens t1 t2 s1 s2 -> PolymorphicLens s1 s2 a1 a2 -> PolymorphicLens t1 t2 a1 a2
compose_lenses lens1 lens2 = PolymorphicLens{get=(get lens2).(get lens1),
                              put=(\t1_elem a2_elem -> (put lens1) t1_elem ((put lens2) ((get lens1) t1_elem) a2_elem))}

rearrange_prod :: (a1->b1,a2->b2) -> (a1,a2) -> (b1,b2)
rearrange_prod (f,g) (x,y) = (f x,g y)
rearrange_prod2 :: (a1->b1->c1,a2->b2->c2) -> (a1,a2) -> (b1,b2) -> (c1,c2)
rearrange_prod2 (f,g) (x,y) = rearrange_prod (f x,g y)

monoidal_product :: PolymorphicLens t1 t2 b1 b2 -> PolymorphicLens s1 s2 a1 a2 -> PolymorphicLens (t1,s1) (t2,s2) (b1,a1) (b2,a2)
monoidal_product lens1 lens2 = PolymorphicLens{get=rearrange_prod ((get lens1),(get lens2)),
                               put=rearrange_prod2 ((put lens1),(put lens2))}

instance (Enum s,Bounded s,Eq t)=>Eq (s -> t) where
    f==g=and [f x==g x | x <- [minBound..maxBound]]
get_put :: MonomorphicLens s a -> (s -> s)
get_put lens = (\s_elem -> (put lens) (s_elem) ((get lens) s_elem))
lawful1 :: (Enum s,Bounded s,Eq s) => MonomorphicLens s a -> Bool
lawful1 lens = (id == (get_put lens))

put_get :: MonomorphicLens s a -> s -> a -> a
put_get lens s_elem a_elem = (get lens) ((put lens) s_elem a_elem)
lawful2 :: (Enum s,Bounded s,Enum a,Bounded a,Eq a) => MonomorphicLens s a -> Bool
lawful2 lens = (const id == (put_get lens))

put_put_1 :: MonomorphicLens s a -> s -> a -> a -> s
put_put_1 lens s_elem a_elem_1 a_elem_2 = p (p s_elem a_elem_1) a_elem_2 where p=(put lens)
put_put_2 :: MonomorphicLens s a -> s -> a -> a -> s
put_put_2 lens s_elem a_elem_1 a_elem_2 = (put lens) s_elem a_elem_2
lawful3 :: (Enum s,Bounded s,Enum a,Bounded a,Eq s) => MonomorphicLens s a -> Bool
lawful3 lens = (put_put_1 lens)==(put_put_2 lens)

lawful :: (Enum s,Bounded s,Enum a,Bounded a,Eq s,Eq a) => MonomorphicLens s a -> Bool
lawful lens = and [f lens | f <-[lawful1,lawful2,lawful3]]

data Adapter s1 s2 a1 a2 = Adapter{
    get_a :: s1 -> a1,
    put_a :: a2 -> s2
}

as_polymorphic_lens :: Adapter s1 s2 a1 a2 -> PolymorphicLens s1 s2 a1 a2
as_polymorphic_lens adapter = PolymorphicLens{get=(get_a adapter),put=(\s1_elem -> (put_a adapter))}

compose_adapters :: Adapter t1 t2 s1 s2 -> Adapter s1 s2 a1 a2 -> Adapter t1 t2 a1 a2
compose_adapters adapter1 adapter2 = Adapter{get_a=(get_a adapter2).(get_a adapter1),
                              put_a=(put_a adapter1).(put_a adapter2)}

from_function_pair :: (s1 -> a1) -> (a2 -> s2) -> Adapter s1 s2 a1 a2
from_function_pair f g = Adapter{get_a=f,put_a=g}
from_function_pair_pl :: (s1 -> a1) -> (a2 -> s2) -> PolymorphicLens s1 s2 a1 a2
from_function_pair_pl f g = as_polymorphic_lens $ from_function_pair f g

data Singleton = Trivial deriving (Eq,Ord,Show)

type Costate s1 s2 = PolymorphicLens s1 s2 Singleton Singleton

type Connector s = Costate s s

identity_connector :: Connector s
identity_connector = PolymorphicLens{get=const Trivial,put=(\s1_elem a2_elem -> s1_elem)}

type State a1 a2 = PolymorphicLens Singleton Singleton a1 a2

from_element :: a1 -> State a1 a2
from_element a1_elem = PolymorphicLens{get=const a1_elem,put=(\s1_elem ->const Trivial)}

data PolymorphicPrism s1 s2 a1 a2 = PolymorphicPrism{
    review :: a2 -> s2,
    matching :: s1 -> Either s2 a1
}

type MonomorphicPrism s a = PolymorphicPrism s s a a

--apply_functor :: (Functor f) => PolymorphicLens s1 s2 a1 a2 -> PolymorphicLens (f s1) (f s2) (f a1) (f a2)

class (Functor f) => StrongFunctor f where
   left_Strength :: (Functor f) => a -> f b -> f (a,b)

instance StrongFunctor Maybe where
   left_Strength a_elem Nothing = Nothing
   left_Strength a_elem (Just b_elem) = Just (a_elem,b_elem)

class (Functor f,Applicative f) => MonoidalFunctor f where
   phi :: (f a1 ,f a2) -> f (a1,a2)
   phiInv :: f (a1,a2) -> (f a1 ,f a2)

modified_star :: (Applicative f) => (f s1 -> f(a2 -> s2)) -> f s1 -> f a2 -> f s2
modified_star before x = (<*>) (before x)

optic_C_to_D :: (Applicative f) => PolymorphicLens s1 s2 a1 a2 -> PolymorphicLens (f s1) (f s2) (f a1) (f a2)
optic_C_to_D lens_c = PolymorphicLens{get = fmap (get lens_c),put = modified_star (fmap (\x->(put lens_c x)))}

class Functor f => OpLaxSumMonoidal f where
     either_functor :: f (Either s2 a1) -> Either (f s2) (f a1)

matching_helper :: (OpLaxSumMonoidal f) => (s1 -> Either s2 a1) -> f s1 -> f (Either s2 a1)
matching_helper g = fmap g

prism_C_to_D :: (Functor f, OpLaxSumMonoidal f) => PolymorphicPrism s1 s2 a1 a2 -> PolymorphicPrism (f s1) (f s2) (f a1) (f a2)
prism_C_to_D prism_c = PolymorphicPrism{review = fmap (review prism_c),
                        matching=either_functor . matching_helper (matching prism_c)}