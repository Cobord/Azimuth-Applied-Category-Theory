class Poset a where
	leq :: a -> a -> Maybe Bool
	poseq :: a -> a -> Maybe Bool
	headgreatest :: [a] -> [Maybe Bool]
	headgreatest [] = []
	headgreatest (x:[]) = []
	headgreatest (x:xs) = [leq z x | z <- xs ]
	poseq x y = do
		z <- leq x y
		w <- leq y x
		Just ( z && w )
	
data SmallExample = Red1 | Yellow2 | Green3 | Blue6

instance Show SmallExample where
	show Red1 = "Red1"
	show Yellow2 = "Yellow2"
	show Green3 = "Green3"
	show Blue6 = "Blue6"

instance Poset SmallExample where
	leq Red1 Red1 = Just True
	leq Red1 Yellow2 = Just True
	leq Red1 Green3 = Just True
	leq Red1 Blue6 = Just True
	leq Yellow2 Yellow2 = Just True
	leq Yellow2 Green3 = Nothing
	leq Yellow2 Blue6 = Just True
	leq Green3 Yellow2 = Nothing
	leq Green3 Green3 = Just True
	leq Green3 Blue6 = Just True
	leq Blue6 Blue6 = Just True
	leq _ _ = Just False
	
data LexicographicProduct = LexicographicProduct {
		 first::SmallExample,
		 second::SmallExample}

instance Poset LexicographicProduct where
	leq l1 l2 = do
		x <- poseq (first l1) (first l2)
		y <- leq (second l1) (second l2)
		z <- leq (first l1) (first l2)
		if (x) then
			Just y
			else Just z