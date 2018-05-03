import Diagrams.Backend.SVG.CmdLine

{-# LANGUAGE NoMonomorphismRestriction #-}
import Diagrams.Prelude
import Data.List
import Data.Ord (comparing)
import Data.Function (on)
import Data.Maybe (fromMaybe)
import Data.Colour.SRGB (sRGB24read)

import qualified Math.Combinatorics.Poset as PS

data Subset = Subset Int [Int]

addDigit :: Int -> Int -> Int
addDigit num d = 10*num+d

name :: Subset -> Int
name (Subset x elts) = foldl addDigit 0 elts
name2 :: [Int] -> Int
name2 elts = foldl addDigit 0 elts

(Subset _ elts1) `isSubset` (Subset _ elts2) = all (`elem` elts2) elts1

subsetsBySize :: Int -> [[Subset]]
subsetsBySize n = map (map (Subset n))
                . groupBy ((==) `on` length)
                . sortBy (comparing length)
                . subsequences
                $ [1..n]

level :: PS.Poset t -> t -> t -> Int
level ps bottom current = length $ PS.interval ps (bottom,current)

level2 :: Eq t => PS.Poset t -> t -> t -> Int
level2 (PS.Poset (set,po)) bottom current = maximum $ 0:[1+ level2 (PS.Poset (set,po)) bottom x | x<- set, x `po` current, x /= current]

breakPosetByLevel :: Eq t => PS.Poset t -> t -> [[t]]
breakPosetByLevel (PS.Poset (set,po)) bottom = groupBy (\x y -> (myLevel x == myLevel y)) $ sortBy (\x y -> (compare (myLevel x) (myLevel y))) set
                                              where myLevel = (\z -> (level2 (PS.Poset (set,po)) bottom z))

node :: Show t => t -> Diagram B
node n = text (show n) # fontSizeL 0.2 # fc white <> square 1 # fc blue

drawElts n elts = hcat
                . map (\i -> if i `elem` elts
                               then node i
                               else strutX 1
                      )
                $ [1..n]

drawSet (Subset n elts) = (drawElts n elts # centerXY
                            <> rect (fromIntegral n + 0.5) 1.5
                                 # dashingG [0.2,0.2] 0
                                 # lw thin
                                 # named (name2 elts)
                          )
drawItem n = node n # named n

hasseRow = centerX . hcat' (with & sep .~ 2) . map drawSet

hasseDiagram n = setsD # centerXY
  where setsD = vcat' (with & sep .~ fromIntegral n)
              . map hasseRow
              . reverse
              $ subsets
        subsets = subsetsBySize n

hasseDiagram2 ps bottom = setsD # centerXY
    where setsD = vcat' (with & sep .~ fromIntegral 1)
           . map (centerX . hcat' (with & sep .~ 2) . map drawItem)
           $ breakPosetByLevel ps bottom

toConnect :: Int -> [(Int,Int)]
toConnect n = concat $ zipWith connectSome (subsetsBySize n) (tail $ subsetsBySize n)
connectSome :: [Subset] -> [Subset] -> [(Int,Int)]
connectSome subs1 subs2 = [ (name s1, name s2) | s1 <- subs1
                                             , s2 <- subs2
                                             , s1 `isSubset` s2 ]

withConnections n = (hasseDiagram n) # applyAll [connectOutside' (with & gaps       .~ small
                          & headLength .~ local 0.15) j k | (j,k) <- toConnect n]

toConnect2:: Eq t => PS.Poset t -> t -> [(t,t)]
toConnect2 ps bottom = concat $ zipWith (connectSome2 ps) (broken) (tail $ broken) where broken=(breakPosetByLevel ps bottom)
connectSome2 :: PS.Poset t -> [t] -> [t] -> [(t,t)]
connectSome2 (PS.Poset (set,po)) layeri layerj = [ (s1, s2) | s1 <- layeri
                                             , s2 <- layerj
                                             , s1 `po` s2 ]
withConnections2 ps bottom = (hasseDiagram2 ps bottom) # applyAll [connectOutside' (with & gaps       .~ small
                          & headLength .~ local 0.15) j k | (j,k) <- toConnect2 ps bottom]

--example = pad 1.1 $ withConnections2 (PS.posetD 24) 1
example = pad 1.1 $ withConnections2 (PS.posetB 5) []

-- Bennett's laws
--data possResources = (0,0,0) | (1,0,0) | (0,1,0) | (0,0,1) | (1,1,0) | (0,0,2)
--resources = [(0,0,0),(1,0,0),(0,1,0),(0,0,1),(1,1,0),(0,0,2)]
-- any resource is better than none
--relation _ (0,0,0) = True
-- 1 qubit is better than or equal to an ebit, cbit or qubit
--relation (1,0,0) _ = True
-- superdense coding
--relation (1,1,0) (0,0,2) = True
--relation (1,1,0) (1,0,0) = True
--relation (1,1,0) (0,1,0) = True
--relation (0,0,2) (0,0,1) = True

--bennetExample = PS.poset(resources,relation)
--example = pad 1.1 $ withConnections2 bennetExample (0,0,0)

main = mainWith (example :: Diagram B)