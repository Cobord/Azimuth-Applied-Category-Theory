{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

data PolymorphicLens s1 s2 a1 a2 = PolymorphicLens{
    get :: s1-> a1,
    put :: s1->a2->s2
}

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