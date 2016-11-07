import System.Random
import Data.Maybe
import Data.Array.ST
import Control.Monad.ST
import Data.STRef
import qualified Data.Set as Set
import Control.DeepSeq
import Control.Monad
import Control.Parallel.Strategies
import Data.List
import Data.Time.Clock.POSIX
import System.Directory

data Tree = Node Int Tree Tree | Empty deriving(Show)

eval :: Tree -> Tree
eval Empty               = Empty
eval (Node n left right) = seq n $ seq left $ seq right $ Node n left right

averageLeafDepth :: Tree -> Double
averageLeafDepth Empty = 0
averageLeafDepth tree = fromIntegral (sum list) / genericLength list
    where 
        leafDepths :: Tree -> Int -> [Int]
        leafDepths Empty depth = [depth]
        leafDepths (Node _ le ri) depth = leafDepths le (depth + 1) ++ leafDepths ri (depth + 1)        
        
        list :: [Int]
        list = leafDepths tree 0
        

-- * Helpers for random values
type RandomValue g a = g -> (a, g)
(>->) :: RandomValue g a -> (a -> b) -> RandomValue g b
(>->) value f gen = (f x, gen')
    where
        (x, gen') = value gen

(>+>) :: RandomValue g a -> (a -> RandomValue g b) -> RandomValue g b
(>+>) value f gen = f x gen'
    where
        (x, gen') = value gen

combine :: (a -> b -> c) -> RandomValue g a -> RandomValue g b -> RandomValue g c
combine f left right gen = (f left' right', gen'')
    where
        (left', gen') = left gen
        (right', gen'') = right gen'

rndConst :: a -> RandomValue g a
rndConst = (,)

rndMap :: (a -> RandomValue g b) -> [a] -> RandomValue g [b]
rndMap _ []       = rndConst []
rndMap f (x : xs) = combine (:) (f x) (rndMap f xs)

rndRepeat :: Int -> RandomValue g a -> RandomValue g [a]
rndRepeat 0 _   = rndConst []
rndRepeat n val = combine (:) val (rndRepeat (n - 1) val)

choose :: RandomGen g => [a] -> RandomValue g a
choose xs = randomR (0, length xs - 1) >-> (xs !!)

-- Shuffle algorithm from https://wiki.haskell.org/Random_shuffle
shuffle :: RandomGen g => [a] -> RandomValue g [a]
shuffle xs gen = runST (do
        g <- newSTRef gen
        let randomRST lohi = do
              (a,s') <- fmap (randomR lohi) (readSTRef g)
              writeSTRef g s'
              return a
        ar <- newArray n xs
        xs' <- forM [1..n] $ \i -> do
                j <- randomRST (i,n)
                vi <- readArray ar i
                vj <- readArray ar j
                writeArray ar j vi
                return vj
        gen' <- readSTRef g
        return (xs',gen'))
  where
    n = length xs
    newArray :: Int -> [a] -> ST s (STArray s Int a)
    newArray m = newListArray (1, m)

takeRandom :: RandomGen g => Int -> [a] -> RandomValue g [a]
takeRandom count xs = shuffle xs >-> take count

takeRandom' :: RandomGen g => Int -> Int -> RandomValue g [Int]
takeRandom' count upper = gen count Set.empty
    where
        gen 0 _   g1 = ([], g1)
        gen c set g1
            | Set.member val set = gen (c-1) set g2
            | otherwise          = gen (c-1)(Set.insert val set) g2
            where
                (val, g2) = randomR (0, upper) g1

-- * Tree manipulations
-- Inserts or removes an element in a tree
toggle :: RandomGen g => Int -> Tree -> g -> (Tree, g)
toggle x Empty = (,) (Node x Empty Empty)            -- Insert in empty tree
toggle x n@(Node a left right)
    | x == a = deleteRoot n   >-> eval                         -- Remove item
    | x >  a = toggle x right >-> eval >-> Node a left         -- Toggle on left side
    | x <  a = toggle x left  >-> eval >-> flip (Node a) right -- Toggle on right side

-- Deletes the root node of a tree
deleteRoot :: RandomGen g => Tree -> g -> (Tree, g)
deleteRoot Empty = rndConst Empty
deleteRoot (Node _ left  Empty) = rndConst left
deleteRoot (Node _ Empty right) = rndConst right
deleteRoot (Node _ left  right) = choose [
        Node (fromJust leftMax)  (eval left') right,
        Node (fromJust rightMax) left  (eval right')
    ] >-> eval
    where
        (left', leftMax) = extractMax left
        (right', rightMax) = extractMin right

-- Extracts the minimum of a tree
-- Returns the resulting tree and the value of the removed node
extractMin :: Tree -> (Tree, Maybe Int)
extractMin Empty = (Empty, Nothing)
extractMin (Node x Empty right) = (right, Just x)
extractMin (Node x left  right) = (Node x left' right, value)
    where
        (left', value) = extractMin left

-- Extracts the maximum of a tree
-- Returns the resulting tree and the value of the removed node
extractMax :: Tree -> (Tree, Maybe Int)
extractMax Empty = (Empty, Nothing)
extractMax (Node x left Empty) = (left, Just x)
extractMax (Node x left right) = (Node x left right', value)
    where
        (right', value) = extractMax right

-- Toggles all elements of a list in a tree
toggleArray :: RandomGen g => Tree -> [Int] -> RandomValue g Tree
toggleArray tree xs g = foldl' reduce (tree, g) xs
    where
        reduce (tree', g') x = toggle x tree' g'

fromList :: RandomGen g => [Int] -> RandomValue g Tree
fromList = toggleArray Empty

build :: RandomGen g => RandomValue g [Int] -> RandomValue g Tree
build gen = gen >+> fromList

-- * Measurements
-- Calculates the height of the tree
calculateHeight :: Tree -> Int 
calculateHeight Empty = -1 --If the tree is empty, 0
calculateHeight (Node _ le ri) = 1 + max (calculateHeight le) (calculateHeight ri) -- 1 plus the maximum of the left tree height or the right tree height

-- Calculates average depth
calculateDepth :: Int -> Tree -> Double
calculateDepth n tree = fromIntegral (calculate tree 0) / fromIntegral n
  where
    calculate Empty        _ = 0
    calculate (Node _ l r) d = d + calculate l (d + 1) + calculate r (d + 1)

-- Calculates the total nodes (Empty leaves don't count)
calculateNodes :: Tree -> Int 
calculateNodes Empty = 0 --If it's empty, 0
calculateNodes (Node _ le ri) = 1 + calculateNodes le + calculateNodes ri --The amount of nodes left plus the amount of nodes right plus this one.

-- Calculates variance in depth of leaves
calculateLeafDepthVariance :: Tree -> Double
calculateLeafDepthVariance = variance . flip (heights 0) []
    where
        heights depth Empty accum = depth : accum
        heights depth (Node _ l r) accum
            = heights (depth + 1) l
            $ heights (depth + 1) r accum

-- * Print helpers
--Print the x'th layer of the tree
printTreeLevel :: Int -> Tree -> String
printTreeLevel _ Empty = "-" --If there is nothing to be print
printTreeLevel 0 (Node x _ _) = show x --We want to print this one
printTreeLevel x (Node a le ri) = printTreeLevel (x-1) le ++ ";" ++ printTreeLevel (x-1) ri --We want to print the lower layers, so print the left side and then the right side.

--Print the complete tree to, and including, the x'th element
printTree :: Int -> Tree -> String 
printTree _ Empty = "" --If there is nothing to print
printTree 0 tree = printTreeLevel 0 tree --Print first layer of the tree
printTree x tree = printTree (x-1) tree ++ "\n" ++ printTreeLevel x tree --Print the level before x, newline, the x'th level.

-- * Generators
genInsertsOnly :: RandomGen g => Int -> RandomValue g [Int]
genInsertsOnly n = shuffle [0 .. n]

genInsertsThenDeletes :: RandomGen g => Int -> Int -> RandomValue g [Int]
genInsertsThenDeletes n k = combine (++) (shuffle ids) (takeRandom k ids)
    where ids = [0 .. n + k - 1]

genInsertsAndDeletes :: RandomGen g => Int -> Int -> RandomValue g [Int]
genInsertsAndDeletes n k = takeRandom k ids >+> (shuffle . (ids ++))
    where ids = [0 .. n + k - 1]

genInsertsLifetime :: RandomGen g => Int -> Int -> Int -> RandomValue g [Int]
genInsertsLifetime n k l gen = (merge inserts deletes, gen'')
    where
        ids = [0 .. n + k - 1]
        (insertIds, gen') = shuffle ids gen
        inserts = zip [0..] insertIds
        (deleteIds', gen'') = takeRandom k ids gen'
        deleteIds = Set.fromList deleteIds'
        deletes = map (\(pos, x) -> (pos + l, x)) $ filter (\(_, x) -> Set.member x deleteIds) inserts
        merge [] [] = []
        merge ((_, x):xs) [] = x : merge xs []
        merge [] ((_, y):ys) = y : merge [] ys
        merge xss@((xPos, x): xs) yss@((yPos, y):ys)
            | xPos <= yPos   = x : merge xs  yss
            | otherwise      = y : merge xss ys


-- * Running
standardSizes :: [Int]
standardSizes = [16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048, 3072, 4096]

data Output a = Output String [Result a]
data Result a = Result
  { resNodes             :: Int
  , resHeight            :: a
  , resDepth             :: a -- Average depth
  , resAvgLeafDepth      :: a
  , resLeafDepthVariance :: a
  } deriving (Eq, Show)

type Output'' = Output Double
type Output' = Output (Measurement Double)

type Result'' = Result Double
type Result' = Result (Measurement Double)

instance NFData a => NFData (Output a) where
  rnf (Output name res) = res `deepseq` name `seq` ()

instance NFData a => NFData (Result a) where
  rnf (Result n h d l v) = n `deepseq` h `deepseq` d `deepseq` l `deepseq` v `deepseq` ()

averageResults :: Fractional a => [Result a] -> Result (Measurement a)
averageResults results@(Result{ resNodes = n }: _) = Result
  { resNodes             = n
  , resHeight            = measure' resHeight
  , resDepth             = measure' resDepth
  , resAvgLeafDepth      = measure' resAvgLeafDepth
  , resLeafDepthVariance = measure' resLeafDepthVariance
  }
  where measure' prop = measure $ map prop results

run :: RandomGen g => Int -> [Int] -> (Int -> RandomValue g [Int]) -> RandomValue g [Result']
run count xs gen = rndMap (\n -> runAverage count n $ gen n) xs

runAverage :: RandomGen g => Int -> Int -> RandomValue g [Int] -> RandomValue g Result'
runAverage count n generator = rndRepeat count (runSingle n generator) >-> averageResults

runSingle :: RandomGen g => Int -> RandomValue g [Int] -> RandomValue g Result''
runSingle n generator = build generator >-> (\tree -> Result
    n
    (fromIntegral (calculateHeight tree))
    (calculateDepth n tree)
    (averageLeafDepth tree)
    (calculateLeafDepthVariance tree))

output :: [Result'] -> String
output results
  = "n;height average;height variance;average depth average;average depth variance;average leaf depth average;average leaf depth variance;leaf depth variance average;leaf depth variance variance;\n"
  ++ foldr (\item rest -> output' item ++ rest) "" results
  where
      output' (Result n h d avld var) = fields
        $  [show n]
        ++ showField h
        ++ showField d
        ++ showField avld
        ++ showField var
      showField (Measurement value var _) = [showNumber value, showNumber var]
      showNumber value = "=\"" ++ show value ++ "\""
      fields = (++ ";\n") . intercalate ";"

runCase :: RandomGen g => Int -> String -> (Int -> RandomValue g [Int]) -> Int -> g -> Output'
runCase count name generator maxSize g = Output name results
    where (results, _) = run count (takeWhile (<= maxSize) standardSizes) generator g

printOutput :: Int -> Output' -> IO ()
printOutput time (Output name results) = do
    putStr $ "\n* " ++ name ++ "\n"
    let res = output results
    putStr res
    writeFile ("output/" ++ show time ++ "/" ++ name ++ ".csv") res

cases :: [(String, Int, Int -> RandomValue StdGen [Int])]
cases =
  [ ("inserts",         maxBound, genInsertsOnly)

  -- linear number of deletes
  , ("ins-then-del-1",  maxBound, \n -> genInsertsThenDeletes n n)
  , ("ins-then-del-10", maxBound, \n -> genInsertsThenDeletes n (n * 10))
  , ("ins-and-del-1",   maxBound, \n -> genInsertsAndDeletes n n)
  , ("ins-and-del-10",  maxBound, \n -> genInsertsAndDeletes n (n * 10))
  , ("ins-lifetime-1",  maxBound, \n -> genInsertsLifetime n n (n `div` 2))
  , ("ins-lifetime-10", maxBound, \n -> genInsertsLifetime n (n * 10) (n `div` 2))
  
  -- quadratic number of deletes
  , ("ins-then-del-n",  2048, \n -> genInsertsThenDeletes n (n * n `div` 8))
  , ("ins-and-del-n",   2048, \n -> genInsertsAndDeletes n (n * n `div` 8))
  , ("ins-lifetime-n",  2048, \n -> genInsertsLifetime n (n * n `div` 8) (n `div` 2))
  
  -- cubic number of deletes
  , ("ins-then-del-n2", 512, \n -> genInsertsThenDeletes n (n * n * n `div` 32))
  , ("ins-and-del-n2",  512, \n -> genInsertsAndDeletes n (n * n * n `div` 32))
  , ("ins-lifetime-n2", 512, \n -> genInsertsLifetime n (n * n * n `div` 32) (n `div` 2))
  ]

-- * Statistics
average :: Fractional a => [a] -> a
average xs = sum xs / fromIntegral (length xs)

variance :: Fractional a => [a] -> a
variance xs = sum (map ((^2) . subtract (average xs)) xs) / fromIntegral (length xs - 1)

data Measurement a = Measurement
  { mAverage  :: a
  , mVariance :: a
  , mCount    :: Int
  }
instance NFData a => NFData (Measurement a) where
  rnf (Measurement a v c) = a `deepseq` v `deepseq` c `seq` ()

measure :: Fractional a => [a] -> Measurement a
measure xs = Measurement (average xs) (variance xs) (length xs)

-- * Main
main :: IO ()
main = do
    let repeatCount = 8

    time' <- getPOSIXTime
    let time = round time'
    createDirectoryIfMissing True ("output/" ++ show time)
    gens <- replicateM (length cases) newStdGen

    let outputData' = map (\(g, (name, maxSize, gen)) -> runCase repeatCount name gen maxSize g) (zip gens cases)
    let outputData  = outputData' `using` parList rdeepseq -- Parallel deepseq on list

    mapM_ (printOutput time) outputData

    return ()
